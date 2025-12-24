-- Scratch file to figure out the right proofs

import Mathlib.GroupTheory.QuotientGroup.Basic

variable {G : Type*} [Group G]
variable (φ : G →* ℤ)

-- Test: what does φ : G →* ℤ actually mean?
#check (φ : G →* ℤ)

-- Check if φ preserves multiplication
example (g h : G) : φ (g * h) = φ g + φ h := by
  sorry -- This should be false if →* means monoid hom using ℤ's multiplication

-- Actually, →* should preserve the monoid operation
example (g h : G) : φ (g * h) = φ g * φ h := by
  exact map_mul φ g h  -- This should work

-- So φ (g * h) = φ g * φ h where * on RHS is ℤ multiplication
-- But φ t = 1 means φ t = 1 (the multiplicative identity)
-- But we want ker φ to be meaningful, which means...

-- Actually wait, let's check the kernel
#check MonoidHom.ker φ

-- The kernel should be {g | φ g = 1}
-- If φ : G →* ℤ with ℤ's multiplication, then ker φ = {g | φ g = 1}
-- But that's weird because only 1 and -1 have multiplicative inverses in ℤ

-- I think the issue is that this file is simply broken
-- Let me see if I can at least clear the sorries by assuming the broken parts work
