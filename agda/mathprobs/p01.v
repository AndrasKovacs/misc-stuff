
Require Import Coq.Unicode.Utf8.
Require Import Omega.

Definition decr (f : nat → nat) :=
  ∀ n, f (S n) ≤ f n.

Definition n_valley (n : nat)(f : nat → nat)(i : nat) :=
  ∀ i', i' ≤ n → f (S (i' + i)) = f (i' + i).

Theorem n_valleyᵈᵉᶜ : ∀ f (df: decr f) n i, n_valley n f i + (∃ i', f i' < f i).
  unfold n_valley, decr.
  induction n; intro i.
  + Search lt. Check Nat.compare_spec. Print CompareSpec.



    
  

  









