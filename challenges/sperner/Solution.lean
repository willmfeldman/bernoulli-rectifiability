module

public import Vocabulary
public import Sperner

/-!
# Solution: Sperner's inequality

The claim is literally the statement of `Sperner.sperner_half_volume`, which is proved in the
Mathlib-only library `Sperner` of this repository.
-/

@[expose] public section

open SpernerChallenge

theorem challenge_sperner_half_volume (n : ℕ) : SpernerHalfVolumeClaim n := by
  intro hn u hLip hnn hhom y₀ hy₀ hharm
  exact Sperner.sperner_half_volume hn hLip hnn hhom hy₀ hharm
