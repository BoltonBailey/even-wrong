/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

/-!
# NotWrong.Demo

Solutions to the challenges in `EvenWrong.Demo`.

Each solved theorem is declared under the **same fully-qualified name** as its
challenge (`EvenWrong.Demo.*`) so that `comparator` can match the two
declarations. This module does not import `EvenWrong`.

`EvenWrong.Demo.two_plus_two` is false, so it has no solution here.
-/

@[expose] public section

namespace EvenWrong.Demo

/-- Solution to `EvenWrong.Demo.nat_add_comm`. -/
theorem nat_add_comm (n m : Nat) : n + m = m + n :=
  Nat.add_comm n m

end EvenWrong.Demo
