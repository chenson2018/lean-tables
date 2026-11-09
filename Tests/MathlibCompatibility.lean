import Mathlib
import Table.Proofs
import Table.ParseCSV
import Tests.TestingNotation

-- Import the full upstream library to catch duplicate public declarations,
-- including declarations outside the smaller Mathlib modules used by Table.
namespace Table.Tests.MathlibCompatibility

example (f : α → β → γ) (a : α) (b : β) : Function.swap f b a = f a b := rfl

-- The old local `not_not` was this constructive implication, not double
-- negation elimination.
example {p : Prop} (h : p) : ¬¬p := not_not_intro h

-- Both commands must retain their own behavior after the combined import.
#test ∀ n : Nat, n + 0 = n

/-- error: Test failed -/
#guard_msgs in
#table_test false

-- Product ordering and repeated elements matter to crossJoin's row order.
#table_test List.product [1, 1, 2] ["a", "b"] =
  [(1, "a"), (1, "b"), (1, "a"), (1, "b"), (2, "a"), (2, "b")]

def left : Table [("n", Nat)] := Table.mk [/[1], /[1], /[2]]
def right : Table [("s", String)] := Table.mk [/["a"], /["b"]]

#table_test crossJoin left right = Table.mk
  [/[1, "a"], /[1, "b"], /[1, "a"], /[1, "b"], /[2, "a"], /[2, "b"]]

#table_test crossJoin left (Table.mk [] : Table [("s", String)]) = Table.mk []
#table_test crossJoin (Table.mk [] : Table [("n", Nat)]) right = Table.mk []

end Table.Tests.MathlibCompatibility
