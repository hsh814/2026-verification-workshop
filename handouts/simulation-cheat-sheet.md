# Simulation cheat sheet

## 먼저 방향을 확인한다

```text
source = specification
target = implementation

ISim source target
ctx_refines target source
Beh(target) ⊆ Beh(source)
```

Target이 source가 허용하지 않은 observable behavior를 새로 만들지 않음을
증명한다. 두 behavior set이 같을 필요는 없으며 target이 source의 nondeterminism을
줄여도 된다.

## Event와 관찰 가능성

| Event | 의미 | 최종 behavior에서 관찰되는가? |
|---|---|---|
| `Choose X` | 프로그램 쪽의 선택 | trace label은 아님; branch behavior의 union |
| `Take X` | 환경/specification 쪽의 임의 응답 | trace label은 아님; branch behavior의 intersection |
| `IO fn args` | 외부 요청과 응답 | 예, 같은 요청을 맞춰야 함 |
| `SGet k` | module-local state 조회 | 아니요; compilation에서 해석 |
| `SPut k v` | module-local state 갱신 | 아니요; compilation에서 해석 |
| `Call fn arg` | linked function 호출 | 아니요; linked body로 해석 |

```text
itree crisE -> linking/local-state interpretation -> itree coreE -> behavior
coreE = Choose | Take | IO
```

## Case를 고르는 질문

1. 양쪽 current head는 무엇인가?
2. 이 step은 observable인가 internal인가?
3. 선택이 있다면 누가 witness를 고르고 누가 모든 경우를 처리하는가?
4. Step 뒤 어느 source/target state를 relation으로 다시 연결할 것인가?

## Simulation case와 tactic

| Current head | proof obligation의 직관 | 주로 쓸 tactic |
|---|---|---|
| `Ret` / `Ret` | return이 postcondition을 만족 | `cStep` |
| source internal step | source만 조용히 진행 | `cStepS`, `cStepsS` |
| target internal step | target만 조용히 진행 | `cStepT`, `cStepsT` |
| 같은 `IO fn args` | 같은 request, 모든 response 뒤 계속 | `cStep` |
| source `Choose X` | target behavior를 설명할 source witness 선택 | `cForceS witness` |
| target `Choose X` | target의 모든 선택 처리 | `cStepT` |
| source `Take X` | source의 모든 응답에서 relation 유지 | `cStepS` |
| target `Take X` | target response witness 선택 | `cForceT witness` |
| `SGet` | 현재 local value를 continuation에 대입 | `cStepS`, `cStepT` |
| `SPut` | state 갱신 뒤 invariant 복원 | `cStepS`, `cStepT` |
| 양쪽의 같은 `Call` | call boundary에서 state relation 전달 | `cCall` |
| 한쪽 call body를 직접 전개 | 해당 body inline | `cInlineS`, `cInlineT` |

Tactic 이름을 먼저 추측하지 말고 선택의 polarity를 말로 확인한다.

## KV–SortedList에서 유지할 relation

```coq
Definition state_rel (m : Z -> option Z) (xs : list (Z * Z)) : Prop :=
  sorted_keys xs /\
  forall k, m k = list_get k xs.
```

- `sorted_keys xs`: key가 strictly increasing하며 따라서 중복 key가 없다.
- Pointwise equality: 모든 query에서 abstract map과 concrete list의 결과가 같다.
- `get`: pointwise equality를 query key에 instantiate한다.
- `put`: 새 map/list를 witness로 고르고 `state_rel_put`을 적용한다.

```coq
state_rel_put :
  state_rel m xs ->
  state_rel (map_put m k v) (list_put k v xs)
```

Target list는 heap이 아니라 module state에 저장된 mathematical list다.
Gallina의 recursive `list_get`/`list_put`은 simulation step으로 한 칸씩 나타나지
않는다.

## Proof가 막히면

- `print 42` 대 `print 43`처럼 I/O request가 다른가? 그렇다면 올바른 simulation이
  없을 수 있으므로 countertrace를 찾는다.
- source/target 순서를 바꾸지 않았는가? `ISim`과 `ctx_refines`의 표기 순서는
  반대다.
- `put` 뒤 옛 state로 relation을 만들고 있지 않은가? 갱신된 `m`과 `xs`를
  witness로 잡는다.
- `Choose`의 witness를 잘못된 쪽에서 고르려 하는가? 위 polarity 표로 돌아간다.
