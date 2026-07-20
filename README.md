# 2026 Verification Workshop

CRIS와 Rocq으로 operational semantics, simulation, module refinement를 익히는
2026 verification workshop 1일차 자료다. 참가자는 Rocq과 program verification을
처음 접한다고 가정한다.

실습의 최종 예제는 다음 refinement다.

```text
source: key-value storage module, state = Z -> option Z
target: sorted-list module, state = list (Z * Z)
```

Target은 heap-linked list가 아니다. Strictly sorted된 mathematical list 전체를
module-local state로 저장하고 `get`과 `put`을 구현한다. 따라서 1일차에는 pointer,
allocation, ownership이 아니라 representation relation과 simulation에 집중한다.

## 일정

총 강의 2시간, 실습 3시간 30분이며 30분 휴식은 실습 시간에 포함하지 않는다.

| 구간 | 시간 | 내용 |
|---|---:|---|
| 이론 1 | 60분 | Rocq 기초와 interaction tree |
| 이론 2 | 60분 | module semantics, behavior, simulation, refinement |
| 실습 1-A | 90분 | compiler-style program pair의 simulation |
| 실습 1-B | 30분 | KV–SortedList 예제와 state relation 도입 |
| 휴식 | 30분 | 휴식 |
| 실습 2 | 90분 | `get`/`put` 및 module refinement proof |

상세 운영안은 [lectures/day1-outline.md](lectures/day1-outline.md), proof 중 참조할
표는 [handouts/simulation-cheat-sheet.md](handouts/simulation-cheat-sheet.md)에 있다.

## 학습 목표

수업이 끝날 때 참가자는 다음을 할 수 있어야 한다.

1. 작은 itree의 현재 event와 observable/internal step을 구분한다.
2. `ctx_refines target source`가 `Beh(target) ⊆ Beh(source)` 방향임을 설명한다.
3. source/target의 현재 head에 맞는 simulation case를 고른다.
4. KV state와 sorted-list state 사이의 relation을 읽고 사용한다.
5. `get`과 `put`의 function simulation에서 relation을 복원한다.
6. function simulation이 module simulation과 contextual refinement로 이어지는
   흐름을 설명한다.

## 저장소 구성

```text
README.md
lectures/day1-outline.md
handouts/simulation-cheat-sheet.md
theories/                       완성 reference definitions/proofs
exercises/*.v                   학생용 starter 4개
checkpoints/*.v                 진도 복구용 checkpoint 5개
```

`theories/`는 강사용 reference solution이다. 학생은 `exercises/`의 starter를
수정하며, 지정 시각에 진도가 늦으면 `checkpoints/`의 이어서 시작할 파일로
이동한다. 파일별 역할은
[exercises/README.md](exercises/README.md)와
[checkpoints/README.md](checkpoints/README.md)에 정리되어 있다.

## 환경과 검증

- 기준 CRIS snapshot: `CRIS-private` commit
  `56a62de13912f282b460e9b806c0fce045e0880c`
- Rocq: 9.0
- 기본 배치: 이 저장소와 `CRIS-private`이 같은 상위 디렉터리에 존재
- Rocq 실행: workspace shim인 `../.tools/codex-coq-bin`만 사용

완성 reference proof, 학생용 starter, checkpoint를 함께 검증한다.

```sh
make check
```

다른 위치에 CRIS가 있다면 `CRIS_DIR`을 명시할 수 있다.

```sh
make check CRIS_DIR=/absolute/path/to/CRIS-private
```

`make check`는 reference theory를 먼저 compile한 뒤 학생용 starter와 checkpoint가
각각 독립적으로 compile되는지 확인하고, 전체 Rocq 파일에 `Admitted`/`admit`이
없는지 검사한다. Starter와 checkpoint에는 다음 단계로 넘어갈 위치를 나타내는
의도적인 `TODO`와 `Abort`만 남아 있다.

## 1일차 범위 밖

Separation logic ownership, resource algebra, prophecy, cancellation, concurrency,
heap allocation, pointer-linked list, general compiler-correctness theorem,
Paco/GPaco의 내부는 필수 범위가 아니다. Pure sorted-list relation을 ownership을
포함하는 spatial relation으로 확장하는 작업은 2일차 주제로 넘긴다.

## 참고

Compiler-style 실습의 교육 순서는
[refinement-tutorial](https://github.com/dongjaelee1/refinement-tutorial)에서 영감을
받았다. 예제와 proof는 기존 코드를 복사하지 않고 CRIS/Rocq 9 환경에 맞게 새로
작성한다.
