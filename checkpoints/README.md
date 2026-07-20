# Workshop checkpoints

이 디렉터리에는 학생별 속도 차이 때문에 다음 학습 목표를 놓치지 않도록,
구간별로 다시 시작할 수 있는 Rocq 파일이 있다.

## 현재 상태

Checkpoint `.v` 파일 5개가 준비되어 있다. 각 파일은 앞 구간의 핵심 proof를
완성한 상태로 제공하고, 이어서 학습할 단계에 `TODO`와 `Abort`를 둔다.

## Checkpoint 파일

| 파일 | 배포 시점 | 포함할 상태 |
|---|---:|---|
| `Checkpoint10_AfterFirstSimulation.v` | compiler tutorial 25분 | 첫 `Ret`/`Tau` simulation 완성 |
| `Checkpoint20_AfterCompilerPairs.v` | compiler tutorial 90분 | 필수 compiler pair 완성 |
| `Checkpoint30_SortedListRelation.v` | 첫 실습 블록 종료 | `state_rel`과 `get` proof 시작점 |
| `Checkpoint40_AfterGet.v` | 둘째 블록 25분 | `simF_get` 완성, `simF_put` 시작점 |
| `Checkpoint50_AfterPutRelation.v` | 둘째 블록 55–65분 | updated `state_rel` 도출, invariant 복원 시작점 |

Checkpoint는 해답을 모두 공개하는 벌점이 아니라, 정해진 시각에 다음 개념을
함께 학습하기 위한 수업 자료다.

## 운영 cut line

- 25분: 첫 proof가 막히면 `Checkpoint10_AfterFirstSimulation.v`로 이동한다.
- 65분: I/O matching이 병목이면 강사 주도로 전환한다.
- 90분: 진도와 무관하게 compiler tutorial을 끝내고 KV–SortedList로 이동한다.
- 첫 블록 115분: relation을 못 정했으면 정의를 공개한다.
- 휴식 시작: 모두 동일한 sorted-list proof 시작점인지 확인한다.
- 둘째 블록 25분: `get`이 미완료면 `Checkpoint40_AfterGet.v`에서 `put`으로 이동한다.
- 둘째 블록 55–65분: relation 복원이 병목이면
  `Checkpoint50_AfterPutRelation.v`를 쓴다.
- 최종 최소선: `get` proof 완성과 `put` 뒤 relation 보존에 대한 설명이다.

## Checkpoint 검증 기준

- 각 파일은 이전 파일을 수정하지 않고 독립적으로 load/compile된다.
- 예상한 theorem과 proof state에서 시작한다.
- 숨긴 proof를 재정의하거나 module name이 충돌하지 않는다.
- Reference solution과 같은 source/target 방향 및 definitions를 사용한다.
- README의 opam 설치 절차를 마친 새 환경에서 모든 checkpoint를 순서와 무관하게
  열 수 있다.
