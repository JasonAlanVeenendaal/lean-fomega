
import LeanSubst
import LeanFomega.Typing
import LeanFomega.Typing.Substitute
open LeanSubst

namespace LeanFomega

def TSet := List Kind -> List Ty -> Term -> Ty -> Prop
def TSet.empty : TSet := λ _ _ _ _ => False
def TRed := List Kind -> List Ty -> Term -> Term -> Prop

def LR := List Kind -> List Ty -> Term -> Prop

def ℛ (S : LR) : LR
| Δ, Γ1, t => ∀ {r Γ2}, Γ1 -⟨r⟩> Γ2 -> S Δ Γ2 t[r]

mutual
  inductive Typing.SnNor : LR -> TSet
  | lam :
    ℛ S1 Δ Γ (λ[A] t) ->
    SnNor S2 Δ (A::Γ) t B ->
    SnNor S1 Δ Γ (λ[A] t) (A -:> B)
  | tlam :
    SnNor S2 (K::Δ) Γ⟨.add 1⟩ t P ->
    SnNor S1 Δ Γ (Λ[K] t) (∀[K] P)
  | neu :
    SnNeu S Δ Γ A K ->
    SnNor S Δ Γ A K
  | red :
    SnRed Δ S Γ A A' ->
    SnNor Δ S Γ A' K ->
    SnNor Δ S Γ A K

  inductive Typing.SnNeu : LR -> TSet
  | var :
    Γ[x]? = some A ->
    SnNeu S Δ Γ #x A
  | app :
    SnNeu S1 Δ Γ f (A -:> B) ->
    SnNor S2 Δ Γ a A ->
    SnNeu S3 Δ Γ (f • a) B
  | tapp :
    SnNeu S1 Δ Γ f (∀[K] P) ->
    P' = P[su a::+0] ->
    SnNeu S3 Δ Γ (f •[a]) P'

  inductive Typing.SnRed : LR -> TRed
  | beta :
    SnNor S1 Δ Γ t A ->
    SnRed S2 Δ Γ ((λ[A] b) • t) b[su t::+0]
  | tbeta :
    SnRed S Δ Γam ((Λ[K] b) •[t]) b[su t::+0:Ty]
  | app :
    SnRed S1 Δ Γ f f' ->
    SnRed S2 Δ Γ (f • a) (f' • a)
  | tapp :
    SnRed S1 Δ Γ f f' ->
    SnRed S2 Δ Γ (f •[a]) (f' •[a])
end

mutual
  theorem Typing.SnNor.rename (m : Δ1 -⟨r⟩> Δ2) : SnNor S Δ1 A K -> SnNor S Δ2 A[r] K := sorry

  theorem Typing.SnNeu.rename (m : Δ1 -⟨r⟩> Δ2) : SnNeu S Δ1 A K -> SnNeu S Δ2 A[r] K := sorry

  theorem Typing.SnRed.rename (m : Δ1 -⟨r⟩> Δ2) : SnRed S Δ1 A B -> SnRed S Δ2 A[r] B[r] := sorry
end

@[simp]
def 𝒱ₖ : Kind -> List Kind -> Ty -> Prop
| A -:> B, Δ, λ[_] t => ∀ {a}, Typing.SnNor (𝒱ₖ A) Δ a A -> Typing.SnNor (𝒱ₖ B) Δ t[su a::+0] B
| _, _, _ => False

structure Typing.SemSubst (Δ1 Δ2 : List Kind) (σ : Subst Ty) where
  act : ∀ {i T}, Δ1[i]? = some T -> SnNor (𝒱ₖ T) Δ2 (σ.act i) T

notation:35 Γ:35 " -⟦" σ "⟧> " Δ:35 => Typing.SemSubst Γ Δ σ

theorem Typing.SemSubst.lift (m : Γ -⟦σ⟧> Δ) A : A::Γ -⟦σ.lift⟧> A::Δ := sorry

theorem Typing.SemSubst.compose (m1 : Γ -⟦σ⟧> Δ) (m2 : Δ -⟨r⟩> Ξ) : Γ -⟦σ ∘ r.to⟧> Ξ := sorry

@[simp]
def SemanticTyping (Δ1 : List Kind) (A : Ty) (K : Kind) :=
  ∀ {σ Δ2}, Δ1 -⟦σ⟧> Δ2 -> Typing.SnNor (𝒱ₖ K) Δ2 A[σ] K

notation:170 Γ:170 " ⊨ₖ " t:170 " : " A:170 => SemanticTyping Γ t A

theorem Typing.fundamental : Δ ⊢ₖ A : K -> Δ ⊨ₖ A : K
| var j, σ, Δ2, h => sorry
| lam j, σ, Δ2, h => sorry
| app j1 j2, σ, Δ2, h => sorry
| all j, σ, Δ2, h => .all $ j.fundamental $ h.lift _
| arrow j1 j2, σ, Δ2, h => .arrow (j1.fundamental h) (j2.fundamental h)

end LeanFomega
