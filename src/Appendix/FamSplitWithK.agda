data ⊤ : Set where
  tt : ⊤

data ℕ : Set where
  suc : ℕ → ℕ

f : ⊤ → Set
f tt = ℕ

g : ∀ x → f x → ⊤
g tt (suc y) = g tt y


