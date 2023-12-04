\begin{code}
{-# OPTIONS --type-in-type --with-K --allow-unsolved-metas #-}


module Tex.Discussion.AlgOrn where

open import Agda.Primitive
  using    ( Level
           ; SSet )
  renaming ( lzero to ℓ-zero
           ; lsuc  to ℓ-suc
           ; _⊔_   to ℓ-max
           ; Set   to Type
           ; Setω  to Typeω )

open import Relation.Binary.PropositionalEquality hiding (J)

open import Data.Unit
open import Data.Empty
open import Data.Vec
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum hiding (map₂)
open import Data.Nat

open import Function.Base

open import Ornament.Desc
open import Ornament.OrnDesc
open import Ornament.Numerical


private variable
  Me Me′ Me″ Me‴ : Meta
  I J K M : Type
  A B C X Y Z : Type
  P P′ : Type
  Γ Δ Θ Λ : Tel P
  D E : DescI Me Γ I
  U V W   : ExTel Γ
  CD CE : ConI Me Γ V I
  V′ W′ : ExTel Δ

open Meta
\end{code}

%<*almost-algorn>
algOrn   : ∀ {J} (D : Desc ∅ I)
         → (⟦ D ⟧D J →₃ J)
         → OrnDesc Plain ∅ id (Σ I (J tt)) fst D
         
algOrnC  : ∀ {W J} (C : Con ∅ V I) (c : Vxf id W V)
         → (∀ p i → ⟦ C ⟧C J (var→par c p) i → J (fst p) i)
         → ConOrnDesc {J = Σ I (J tt)} Plain c fst C

algOrn []       ϕ  = []
algOrn (C ∷ D)  ϕ  = algOrnC C id (λ p i x → ϕ (fst p) i (inj₁ x))
                   ∷ algOrn D λ p i x → ϕ p i (inj₂ x)

algOrnC  (𝟙 j) c ϕ = 𝟙 (λ pv → j (var→par c pv) , ϕ pv _ refl) (λ a → refl)
algOrnC  {J = J} (ρ g j C) c ϕ
         = OΔσ+ (λ { (_ , pw) → J _ (j (var→par c (_ , pw))) })
         ( Oρ0 (λ { (_ , (pw , i)) → j (var→par c (_ , pw)) , i }) (λ a → refl)
         ( algOrnC C (c ∘ fst) λ { (_ , (pw , j)) i x → ϕ (_ , pw) i (j , x) }))
algOrnC  (σ S h C) c ϕ
         = Oσ+ S
         ( algOrnC  C (h ∘ Vxf-▷ c S)
                    (λ { (_ , (pw , s)) i x → ϕ (_ , pw) i (s , x) }))
algOrnC  {I = I} {J = J} (δ g j R C) c ϕ
         = δ R g j
         ( algOrnC  C c
                    (λ { (_ , w) i x → ϕ (_ , w) i ({!!} , x) }))
%</almost-algorn>

%<*almost-algorn2>
algOrn2  : ∀ {J : ⊤ → ⊤ → Type} (D : DescI Me Γ ⊤)
         → MetaF Me Number
         → (∀ p i → ⟦ D ⟧D (λ _ _ → J tt tt) p i → J tt tt)
         → OrnDesc Plain Γ id (J tt tt) ! D
         
algOrn2C  : ∀ {W} {J : ⊤ → ⊤ → Type} (C : ConI Me Γ V ⊤)
          → MetaF Me Number
          → (c : Vxf id W V)
          → (∀ p i → ⟦ C ⟧C (λ p i → J tt tt) (var→par c p) i → J tt tt)
          → ConOrnDesc {Δ = Γ} {W = W} {J = J tt tt} Plain c ! C

algOrn2 []       iff ϕ  = []
algOrn2 (C ∷ D)  iff ϕ  = algOrn2C C iff id (λ p i x → ϕ (fst p) i (inj₁ x))
                        ∷ algOrn2 D iff λ p i x → ϕ p i (inj₂ x)

algOrn2C  (𝟙 j) iff c ϕ = 𝟙 (λ pv → ϕ pv tt refl) (λ a → refl)
algOrn2C  {J = J} (ρ j g C) iff c ϕ
          = OΔσ+ (λ _ → J tt tt)
          ( ρ (λ { (_ , (_ , i)) → i }) g (λ _ → refl) (λ a → refl)
          ( algOrn2C C iff (c ∘ fst) λ { (p , w , j) i x → ϕ (p , w) tt (j , x) }))
algOrn2C  (σ S h C) iff c ϕ
          = Oσ+ S
          ( algOrn2C C iff (h ∘ Vxf-▷ c S)
                    λ { (p , w , s) i x → ϕ (p , w) i (s , x) })
algOrn2C  {J = J} (δ {me = me′} {iff = iff′} j g R h C) iff c ϕ
          with iff .δf _ _ me′
... | refl , refl , _
          = OΔσ+ (λ { w → μ R (g (var→par c w)) (j (var→par c w)) } )
          ( O∙δ+ {!!} ! (algOrn2 R (iff ∘MetaF iff′) {!didn't think about what J would actually be here!}) (λ _ _ → refl) (λ _ _ → refl) (algOrn2C C iff _ λ { (p , (w , r) , z) i x → ϕ (p , w) tt
          (r , subst (λ a → ⟦ C ⟧C (λ _ _ → J tt tt) (p , h (c w , a)) tt) {!reassuringly/unfortunately?, this is blocked by the same problem as indexed numerical representations!} x) }))
%</almost-algorn2>


-- shortcut is algOrn applied to (toDesc OD) with (ornAlg OD)

shortcut  : {D : DescI Me ∅ ⊤} {E : DescI Me ∅ ⊤} (OD : OrnDesc Plain Γ ! I ! D)
          → MetaF Me Number
          → OrnDesc Me Γ id (Σ I λ i → μ E _ _) fst (toDesc OD)
         
shortcutC  : ∀ {E : DescI Me ∅ ⊤} {U W} {f : Vxf ! W V} {g : Vxf id U W}
           → {C : ConI Me ∅ V ⊤}
           → (OC : ConOrnDesc {Δ = Γ} {W = W} {J = I} Plain f ! C)
           → MetaF Me Number
           → ConOrnDesc {Δ = Γ} {W = U} {J = Σ I λ i → μ E _ _} Me g fst (toCon OC)

shortcut [] iff = []
shortcut (OC ∷ OD) iff
  = shortcutC OC iff 
  ∷ shortcut OD iff  

shortcutC (𝟙 j′ x₁) iff = 𝟙 (λ pv → {!still need a ⟦ toDesc OC ⟧C (~~ μ E ~~) →₃ ~~ μ E ~~ like object here!}) {!!}
shortcutC (ρ j′ h x₁ x₂ OC) iff = {!!}
shortcutC (σ S h v′ x₁ OC) iff = {!!}
shortcutC (δ R j t h x₁ OC) iff = {!!}
shortcutC (Δσ S h v′ x₁ OC) iff = {!!}
shortcutC (Δδ R j t h x₁ OC) iff = {!!}
shortcutC (∙δ m fΛ RR′ h p₁ p₂ OC) iff = {!!}
