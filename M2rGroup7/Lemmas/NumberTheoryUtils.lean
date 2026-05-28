import Mathlib

/-- Two distinct primes are coprime. -/
lemma Nat.Prime.coprime_of_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Nat.Coprime p q :=
  hp.coprime_iff_not_dvd.mpr fun hdvd =>
    hpq ((hq.eq_one_or_self_of_dvd p hdvd).resolve_left hp.one_lt.ne')
