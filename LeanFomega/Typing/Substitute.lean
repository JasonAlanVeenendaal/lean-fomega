
import LeanFomega.Typing
import LeanFomega.Typing.Rename
import LeanFomega.Kinding.Substitute
open LeanSubst

namespace LeanFomega

structure TypingSubst (σ : Subst Term) (Δ : List Kind) (Γ1 Γ2 : List Ty) where
  act : ∀ {x T}, Γ1[x]? = some T -> Δ&Γ2 ⊢ σ.act x : T

notation:1000 Δ:1000 " ⊢ₛ " Γ1:1000 " -[" σ "]> " Γ2:1000 => TypingSubst σ Δ Γ1 Γ2

theorem TypingSubst.re (j : Γ2[y]? = some A) (m : Δ ⊢ₛ Γ1 -[σ]> Γ2)
  : Δ ⊢ₛ (A::Γ1) -[re y::σ]> Γ2 := sorry

theorem TypingSubst.su (j : Δ&Γ2 ⊢ a : A) (m : Δ ⊢ₛ Γ1 -[σ]> Γ2)
  : Δ ⊢ₛ (A::Γ1) -[su a::σ]> Γ2 := sorry

theorem Typing.comp : Δ ⊢ₛ A -[σ]> B -> Δ ⊢ₛ B -[τ]> C -> Δ ⊢ₛ A -[σ ∘ τ]> C := sorry

theorem Typing.subst (m : Δ ⊢ₛ Γ1 -[σ]> Γ2) : Δ&Γ1 ⊢ A : K -> Δ&Γ2 ⊢ A[σ] : K := sorry

theorem Typing.beta : Δ&(A::Γ) ⊢ b : B -> Δ&Γ ⊢ t : A -> Δ&Γ ⊢ b[su t::+0] : B := sorry

end LeanFomega
