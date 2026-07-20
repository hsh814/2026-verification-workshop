# Student exercises

이 디렉터리에는 학생이 직접 수정하는 starter 파일이 있다.

## 현재 상태

학생용 `.v` starter 4개가 준비되어 있다. 각 파일은 완성 definition과 theorem
statement를 import하고, 학생이 채울 단계에 `TODO`와 `Abort`를 둔다.
`theories/*.v`는 강사용 reference solution이므로 수업 중 직접 수정하지 않는다.

## 파일과 학생 작업

| 파일 | 시간 | 학생이 채울 핵심 |
|---|---:|---|
| `Exercise00_RocqCheck.v` | 수업 전 | import와 환경 확인 |
| `Exercise10_SimulationCases_Start.v` | 25분 | `Ret`/`Tau`와 source `Choose` |
| `Exercise20_CompilerPairs_Start.v` | 65분 | internal state, observable I/O, bad-I/O counterexample |
| `Exercise32_KVSortedList_Start.v` | 도입 30분 + proof 90분 | `state_rel` 사용, `simF_get`, `simF_put`, module 조립 |

Starter에는 다음을 완성해서 제공한다.

- imports, CRIS context와 typed function/module boilerplate
- source/target program 및 module definitions
- argument parsing, casts, failure branches
- `list_get`, `list_put`, `sorted_keys`
- `sorted_keys_put`, `list_get_put`, `state_rel_put`의 완성 proof
- 모든 theorem statement

학생에게 남길 핵심은 다음과 같다.

1. Simulation/refinement 방향을 고른다.
2. Current event에 맞는 simulation case를 적용한다.
3. KV map과 sorted list를 strict sortedness 및 pointwise lookup으로 연결한다.
4. `get`의 같은 return value를 relation에서 얻는다.
5. `put` 뒤 갱신된 state witness와 `state_rel_put`으로 relation을 복원한다.
6. Per-function proof를 module simulation으로 조립하고 adequacy의 방향을 확인한다.

학생이 직접 작성하는 KV–SortedList 핵심 proof는 약 25줄을 목표로 한다. Pure
list induction과 module simulation을 동시에 필수로 요구하지 않는다.

## 필수선과 stretch goal

- 전원: first simulation case와 refinement 방향 문제
- 다수: compiler-style 필수 pair와 `simF_get`
- 수업 목표: `simF_put` 뒤 relation 복원
- Stretch: module simulation, adequacy, 또는 pure helper lemma의 induction 한 branch

전체 `ctx_refines`를 각 학생의 필수 완료선으로 삼지 않는다. 지정 시각에 진도가
늦으면 [checkpoints](../checkpoints/README.md)를 사용해 다음 학습 목표로 이동한다.

## Starter 검증 기준

- Reference solution이 `make check`로 `Admitted` 없이 compile된다.
- Starter가 같은 환경에서 각 의도된 hole 직전까지 load된다.
- Hole 이외의 boilerplate에서 학생이 막히지 않는다.
- `ISim source target`과 `ctx_refines target source` 방향이 모든 파일에서 같다.
- Rocq 초심자 dry run에서 `90 + 30 + (휴식 30) + 90` cut line을 지킨다.
