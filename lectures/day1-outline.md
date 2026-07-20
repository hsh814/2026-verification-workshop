# Day 1 outline: module semantics and refinement

## 수업의 목적지

하루 동안 반복해서 보여 줄 최종 방향은 다음과 같다.

```text
ISim source target
  -> behavior inclusion
  -> ctx_refines target source
```

마지막 예제에서는 KV module이 source specification이고, mathematical sorted-list
module이 target implementation이다.

```text
Beh(SortedListTarget) ⊆ Beh(KVSource)
```

## 이론 1: Rocq과 interaction tree — 60분

이 파트는 뒤 강의와 실습을 위한 최소 handoff contract다.

| 시간 | 내용 | 종료 시 할 수 있어야 하는 것 |
|---:|---|---|
| 0–12분 | sentence 실행, goal과 context | 가정과 목표 구분 |
| 12–25분 | `intros`, `destruct`, `exists`, `reflexivity`, `rewrite` | 작은 equality와 witness 처리 |
| 25–42분 | `Ret`, `Tau`, `Vis`, `trigger`, bind | 다음 itree head 찾기 |
| 42–55분 | `Choose`, `Take`, `IO`와 continuation | 선택의 주체와 후속 입력 설명 |
| 55–60분 | trace 예측 문제 | `Tau`와 `IO`의 관찰 가능성 구분 |

Induction/coinduction 일반론보다 당일 파일에서 실제로 읽고 쓸 문법을 우선한다.

## 이론 2: module semantics, simulation, refinement — 60분

KV–SortedList를 처음부터 running example로 사용한다.

| 시간 | 내용 | 확인 질문 |
|---:|---|---|
| 0–5분 | 최종 theorem과 source/target | 왜 포함 방향이 `SortedList -> KV`인가? |
| 5–17분 | module과 local state | `SGet`/`SPut`은 어느 state를 다루는가? |
| 17–27분 | linking과 `Call` | 함수 이름은 언제 body로 해석되는가? |
| 27–38분 | compile pipeline과 behavior | 최종 trace에 남는 event는 무엇인가? |
| 38–46분 | refinement와 contextual refinement | implementation이 nondeterminism을 줄여도 되는가? |
| 46–57분 | simulation relation과 case | 현재 head에서 누가 witness를 고르는가? |
| 57–60분 | KV–SortedList preview | map과 list를 무엇으로 연결하는가? |

### 계속 재사용할 그림

```text
function body : itree crisE
  | Choose / Take / IO
  | SGet / SPut
  | Call
  v
linked module
  | local-state transition과 callee resolution
  v
LMod.compile : itree coreE
  | coreE = Choose | Take | IO
  v
Beh.of_itree : set of traces
```

`SGet`, `SPut`, `Call`은 function body에는 나타나지만 최종 observable event가
아니다. Module compilation과 linking 과정에서 해석된다.

Behavior는 `done`, `abort`, `spin`, `hang`, `interact`를 구분한다. 1일차에는
유한·무한 behavior의 모양과 직관까지만 다루고 adequacy나 coinduction proof의
내부는 펼치지 않는다.

## 실습 블록 1-A: compiler-style simulation — 90분

목표는 compiler를 구현하는 것이 아니라 작은 source/target program pair로
simulation case를 반복하는 것이다.

| 시간 | 문제 | 핵심 감각 |
|---:|---|---|
| 0–10분 | program pair의 behavior와 방향 예측 | target behavior inclusion |
| 10–25분 | `Ret 42` 대 추가 `Tau` | raw case와 tactic의 관계 |
| 25–45분 | scratch local에 저장 후 조회 | one-sided internal step |
| 45–65분 | 내부 계산 뒤 같은 `print 42` | observable I/O lockstep |
| 65–80분 | nondeterministic source, deterministic target | source `Choose` witness |
| 80–90분 | `print 42` 대 `print 43` | countertrace와 proof failure |

설명용 program pair는 다음과 같다. 실제 파일에서는 CRIS syntax와 type wrapper를
완성해 제공한다.

```text
source: Ret 42
target: Tau; Tau; Ret 42

source: Ret (40 + 2)
target: SPut tmp 40; x <- SGet tmp; Ret (x + 2)

source: IO "print" 42; Ret unit
target: SPut tmp 40; x <- SGet tmp; IO "print" (x + 2); Ret unit

source: b <- Choose bool; Ret (if b then 0 else 1)
target: Ret 0

bad source: IO "print" 42; Ret unit
bad target: IO "print" 43; Ret unit
```

첫 program pair만 semantic simulation case로 한 번 전개하고, 이후에는
WSim/ISim tactic을 사용한다. Loop, general compiler theorem, Paco/GPaco는 필수
문제에서 제외한다.

## 실습 블록 1-B: KV–SortedList 도입 — 30분

휴식 전에 proof syntax보다 representation relation을 확정한다.

| 시간 | 활동 |
|---:|---|
| 0–15분 | front/middle/end insert, overwrite, missing-key `get` 손 실행 |
| 15–25분 | source map과 target list state 비교, relation을 종이에 작성 |
| 25–30분 | relation skeleton 확인, 공통 checkpoint로 이동 |

고정 사양은 다음과 같다.

```text
get : Z -> option Z
put : Z * Z -> unit

source state: Z -> option Z
target state: list (Z * Z), key는 strictly increasing
initial states: empty_map / []
missing key: None
duplicate key: 기존 value를 overwrite
```

Target은 heap-linked list가 아니다. List 전체를 한 module-local value로
`SGet`/`SPut`하며 Gallina recursion은 itree step이나 behavior에 나타나지 않는다.
따라서 cost와 memory layout이 아니라 functional behavior를 refinement한다.

핵심 relation은 다음 모양이다.

```coq
Definition state_rel (m : Z -> option Z) (xs : list (Z * Z)) : Prop :=
  sorted_keys xs /\
  forall k, m k = list_get k xs.
```

## 휴식 — 30분

휴식은 3시간 30분의 실습 시간 밖이다. 휴식 전에 relation을 공개하고 동일한
KV–SortedList proof 시작점으로 맞춘다.

## 실습 블록 2: KV–SortedList refinement — 90분

Pure list correctness lemma와 CRIS module boilerplate는 강사가 제공한다. 학생은
state relation을 이용해 itree/module simulation을 닫는다.

| 시간 | 활동 | 핵심 proof step |
|---:|---|---|
| 0–25분 | `simF_get` | 양쪽 state 조회, pointwise lookup으로 return 일치 |
| 25–65분 | `simF_put` | 갱신 state witness, `state_rel_put`으로 relation 복원 |
| 65–80분 | module simulation | 초기 relation과 두 function theorem 조립 |
| 80–87분 | adequacy | `ISim source target`에서 `ctx_refines target source` |
| 87–90분 | exit ticket | relation에 ownership이 들어가면 무엇이 달라지는가? |

필수 학생 proof에서 사용할 helper는 완성해 제공한다.

```coq
sorted_keys_put :
  sorted_keys xs -> sorted_keys (list_put k v xs)

list_get_put :
  list_get q (list_put k v xs) =
  map_put (fun q => list_get q xs) k v q

state_rel_put :
  state_rel m xs ->
  state_rel (map_put m k v) (list_put k v xs)
```

전체 학생의 최소 완료선은 `get` proof와 `put` 후 relation이 보존되는 이유를
설명하는 것이다. 65분 시점에 `put`이 끝나지 않아도 module 조립 설명에는 함께
참여시킨다. 전체 `ctx_refines` theorem은 수업의 목적지지만 개인별 필수 완료선은
아니다.

## 강사가 숨길 것

- `Any` cast와 argument parsing의 실패 branch
- mask, `Program Definition`, module well-formedness boilerplate
- MSim/LSim, Paco/GPaco, adequacy proof의 내부
- pure sortedness 및 lookup-preservation induction 전체
- separation logic ownership과 resource algebra

학생용 starter, checkpoint, solution의 표기 방향을 모두 다음과 같이 유지한다.

```text
simulation: source, target
refinement: target, source
```
