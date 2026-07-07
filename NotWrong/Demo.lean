/-!
# NotWrong.Demo

Solutions to the challenges in `EvenWrong.Demo`.

Each solved theorem is declared under the **same fully-qualified name** as its
challenge (`EvenWrong.Demo.*`) so that `comparator` can match the two
declarations. This module does not import `EvenWrong`.

`EvenWrong.Demo.two_plus_two` is false, so it has no solution here.
-/

namespace EvenWrong.Demo

/-- Solution to `EvenWrong.Demo.nat_add_comm`. -/
theorem nat_add_comm (n m : Nat) : n + m = m + n :=
  Nat.add_comm n m

end EvenWrong.Demo
