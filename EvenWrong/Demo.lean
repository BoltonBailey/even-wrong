/-!
# EvenWrong.Demo

Example *challenges*. Every theorem in this module is stated with a `sorry`
proof. A challenge is "solved" when `NotWrong` contains a theorem with an
identical statement and a real proof, and `comparator` accepts the pair (see
`comparator/Demo.json`).

This module deliberately mixes a provable statement with a false one to
demonstrate that the `EvenWrong` library tolerates wrong statements.
-/

namespace EvenWrong.Demo

/-- A true statement that is easy to prove. `NotWrong.Demo` discharges it. -/
theorem nat_add_comm (n m : Nat) : n + m = m + n := by
  sorry

/-- A **false** statement. It is allowed to live here ("even wrong"), but it
can never be solved in `NotWrong`, so it stays an open `sorry` forever. -/
theorem two_plus_two : 2 + 2 = 5 := by
  sorry

end EvenWrong.Demo
