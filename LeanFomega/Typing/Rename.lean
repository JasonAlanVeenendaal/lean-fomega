
import LeanFomega.Typing
import LeanFomega.Kinding.Rename
import LeanFomega.Kinding.Substitute
open LeanSubst

namespace LeanFomega

structure TypingRen (r : Ren) (Γ1 Γ2 : List Ty) where
  act : ∀ {x T}, Γ1[x]? = some T -> Γ2[r.act x]? = some T

notation:35 Γ:35 " -⟨" r "⟩> " Δ:35 => TypingRen r Γ Δ

theorem TypingRen.lift {Γ1 Γ2 : List Ty} A : Γ1 -⟨r⟩> Γ2 -> A::Γ1 -⟨r.lift⟩> A::Γ2 := sorry

theorem TypingRen.id (X : List Ty) : X -⟨.id⟩> X := sorry

theorem TypingRen.succ {X : List Ty} : X -⟨Ren.add 1⟩> A::X := sorry

theorem TypingRen.comp {A B C : List Ty} : A -⟨r1⟩> B -> B -⟨r2⟩> C -> A -⟨r1 ∘ r2⟩> C := sorry

def Typing.rename_type {Δ1 Δ2 : List Kind} (m : Δ1 -⟨r⟩> Δ2)
  : Δ1&Γ ⊢ t : A -> Δ2&Γ⟨.add 1⟩ ⊢ t : A⟨r⟩ := sorry

def Typing.rename {Δ1 Δ2 : List Kind} {Γ1 Γ2 : List Ty}
  (m1 : Δ1 -⟨r1⟩> Δ2) (m2 : Γ1 -⟨r2⟩> Γ2)
  : Δ1&Γ1 ⊢ t : A -> Δ2&Γ2⟨r1⟩ ⊢ t⟨r2⟩[r1:Ty] : A⟨r1⟩
| var h j => sorry
| lam j1 j2 => sorry
| app j1 j2 => sorry
| tlam j => sorry
| tapp (P := P) j1 j2 e =>
  tapp (P := P⟨r1.lift⟩) (j1.rename m1 m2) (j2.subst m1.to)
    (by
      rw [Subst.apply_stable r1.lift r1.to.lift Ren.to_lift]
      rw [Subst.apply_stable r1 r1.to rfl]
      simp [e]; sorry)

end LeanFomega
