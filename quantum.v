From mathcomp Require Import all_ssreflect all_algebra all_field.
Require Import s2int.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory zmodp.
Open Scope ring_scope.
Open Scope S2I_scope.

Section Quantum.

Lemma conjC_sqrt2 : (sqrtC 2%:R)^* = (sqrtC 2%:R) :> algC.
Proof. by rewrite conj_Creal // Creal_s2Int // sQ2_proof. Qed.

Lemma sqrt2_neq0 : sqrtC 2%:R != 0 :> algC.
Proof. by rewrite sqrtC_eq0 (eqC_nat 2 0). Qed.

Lemma sqrt2X_neq0 k : sqrtC 2%:R ^+ k != 0 :> algC.
Proof.  by rewrite expf_neq0 // sqrt2_neq0. Qed.

Lemma conj_s2Int x : x \is a s2Int -> x^* = x.
Proof. by move=> H; rewrite conj_Creal // Creal_s2Int. Qed.


Definition o2 : 'I_3 := Ordinal (isT: 2 < 3)%N.
Definition o3E (i : 'I_3) : [||i == 0, i ==1 | i == o2].
Proof. by case: i => [] [|[|[|]]]. Qed.

Lemma sum3E (R :ringType) (F : 'I_3 -> R) : 
  \sum_(i < 3)  F i = F 0 + F 1 + F o2.
Proof.
rewrite !big_ord_recl /= big_ord0 addr0 !addrA.
by congr (F _ + F _ + F _); apply/val_eqP.
Qed.

(* conjugate transpose *)
Definition trCmx m n (M : 'M_(m,n)) := map_mx (conjC : algC -> _) (trmx M).

Notation "M ^T*" := (trCmx M) (at level 10).

Lemma trCmx_const n a : (a%:M)^T* = a^*%:M :> 'M_n.
Proof.
rewrite /trCmx tr_scalar_mx.
by apply/matrixP=> i j; rewrite !mxE; case: eqP; rewrite ?rmorph0.
Qed.

Lemma trCmx0 n : 0^T* = 0 :> 'M[algC]_n.
Proof.
have <-: 0%:M = 0 :>  'M[algC]_n by apply/matrixP=> i j; rewrite !mxE mul0rn.
by rewrite trCmx_const conjC0.
Qed.

Lemma trCmx1 n : (1%:M)^T* = 1%:M :> 'M[algC]_n.
Proof. by rewrite trCmx_const conjC1. Qed.

Lemma trCmxN n (M : 'M[algC]_n) : (-M)^T* = - (M^T* ).
Proof. by rewrite -[RHS]map_mxN -raddfN. Qed.

Lemma trCmx_mul m n p (A : 'M_(m, n)) (B : 'M_(n, p)) :
   (A *m B)^T* = B^T* *m A^T*.
Proof. by rewrite /trCmx -!map_trmx map_mxM trmx_mul. Qed.

Lemma trmx_eq0 m n (R: ringType) (M : 'M[R]_(m, n)) : (M  ^T == 0) = (M == 0).
Proof.
apply/eqP/eqP => [H|->]; last by rewrite trmx0.
by rewrite -[M]trmxK H trmx0.
Qed.

Lemma trCmx_eq0 m n (M : 'M_(m, n)) : (M  ^T* == 0) = (M == 0).
Proof. by rewrite map_mx_eq0 trmx_eq0. Qed.

Lemma trCmxK n : cancel (@trCmx n n) (@trCmx n n).
Proof.
move=> u.
rewrite /trCmx map_trmx trmxK .
by apply/matrixP=> i j; rewrite !mxE conjCK.
Qed.

Lemma trCmxZ m n (M : 'M_(m,n)) c :
  (c *: M)^T* = c^* *: M^T*.
Proof. by apply/matrixP=> i j; rewrite !mxE rmorphM. Qed.

Lemma mulmxkC n (R : idomainType) (A B : 'M[R]_n) c : 
   c != 0 -> A *m B = c%:M -> B *m A = c%:M.
Proof.
move=> nZc AB1; pose A' := \det B *: \adj A.
have kA: A' *m A = (c ^+ n)%:M.
  by rewrite -scalemxAl mul_adj_mx scale_scalar_mx mulrC -det_mulmx AB1 det_scalar.
have nZcn : c ^+ n != 0 by apply: expf_neq0.
apply: (scalemx_inj nZcn).
rewrite -mul_scalar_mx -kA !mulmxA -(mulmxA A') AB1.
by rewrite scalar_mxC -mulmxA kA -mul_scalar_mx -!scalar_mxM mulrC.
Qed.

Lemma trCmx_tr m n (M : 'M_(m, n)) :
  (forall i j, M i j \is Creal) -> trCmx M = M^T.
Proof. by move=> H; apply/matrixP => i j; rewrite !mxE (CrealP (H _ _ )). Qed.

(* Unitary *)
Definition mxunitary {n} :=
 [qualify M |  M *m (M : 'M_n) ^T* == 1%:M].

Lemma mxunitaryP n (M : 'M_n) :
  reflect 
   (forall i  j : 'I_n, 
     \sum_(k < n) (M i k * (M j k)^*) = (i == j)%:R)
   (M \is mxunitary).
Proof.
apply: (iffP eqP) => [/matrixP H i j| H].
  have := H i j.
  by rewrite !mxE => <-; apply: eq_bigr => k; rewrite !mxE.
apply/matrixP=> i j.
by rewrite !mxE -H; apply: eq_bigr => k; rewrite !mxE.
Qed.

Lemma mxunitary1 n : (1%:M : 'M_n) \is mxunitary.
Proof. by rewrite qualifE /mxunitary mul1mx trCmx_const conjC1. Qed. 

Lemma mxunitaryN (n : nat) : 
  {in mxunitary, forall M : 'M_n, - M \in mxunitary}.
Proof.
case: n => [|n] M H.
  by rewrite (_ : -M = M) //; apply/matrixP=> [] [].
apply/eqP.
rewrite -{2}scaleN1r trCmxZ rmorphN rmorph1 scaleN1r.
rewrite mulmxN mulNmx opprK.
by apply/eqP.
Qed.

Lemma mxunitaryM n  : 
   {in mxunitary &, forall M1 M2 : 'M_n, M1 *m M2 \in mxunitary}.
Proof.
move=> M1 M2 /eqP H1 /eqP H2; apply/eqP.
rewrite trCmx_mul mulmxA -[_ *m M2 ^T*]mulmxA H2.
by rewrite scalar_mxC -mulmxA H1 mul1mx.
Qed.

Lemma mxunitaryT n (M : 'M_n) : M ^T* \is mxunitary = (M \is mxunitary).
Proof.
rewrite qualifE /mxunitary trCmxK.
by apply/eqP/eqP=> H; rewrite (mulmxkC (@oner_neq0 _)).
Qed.

(* All the scaled elements are in s2Int *)

Definition mxs2int {n} m := 
 [qualify M | 
   [forall i : 'I_n, forall j : 'I_n, (sqrtC 2%:R ^+ m) * (M : 'M_n) i j \is a s2Int]].

Notation " m .-s2int" := (mxs2int m) (format "m .-s2int", at level 10).

Lemma mxs2intP n m  (M : 'M_n) : 
  reflect (forall i j,  (sqrtC 2%:R) ^+ m * M i j \is a s2Int) 
          (M \is m.-s2int).
Proof.
apply: (iffP forallP) => [H i j|H i]; first by have /forallP/(_ j) := H i.
by apply/forallP=> j; apply: H.
Qed.

Lemma mxs2int1 n : (1%:M : 'M_n) \is 0.-s2int.
Proof.
apply/forallP=> i; apply/forallP=> j; rewrite mul1r mxE.
by case: eqP; rewrite (rpred0, rpred1).
Qed.

Lemma mxs2intW n m1 m2  (M : 'M_n) : 
  (m1 <= m2)%N -> M \is m1.-s2int -> M \is m2.-s2int.
Proof.
move=> /subnK<- /mxs2intP Hm; apply/mxs2intP=> i j.
by rewrite exprD -mulrA rpredM // rpredX // sQ2_proof.
Qed.

Lemma mxs2intM n m1 m2 (M1 M2 : 'M_n) : 
  M1 \is m1.-s2int -> M2 \is m2.-s2int -> M1 *m M2 \is (m1 + m2).-s2int.
Proof.
move=> /mxs2intP HS1 /mxs2intP HS2; apply/mxs2intP=> i j.
rewrite !mxE !mulr_sumr rpred_sum // => k _.
by rewrite exprD -mulrA [_ * (M1 _ _ * _)]mulrCA !mulrA -mulrA rpredM.
Qed.

Lemma mxs2intT n m (M : 'M_n) : (M ^T* \is m.-s2int) = (M \is m.-s2int).
Proof.
apply/mxs2intP/mxs2intP => H i j; have := H j i; rewrite !mxE => H1.
  by rewrite  -[_ * _]conjCK s2Int_conj // rmorphM rmorphX conjC_sqrt2.
by rewrite -conjC_sqrt2 -rmorphX -rmorphM s2Int_conj.
Qed.

Lemma mxs2int_tr n m (M : 'M_n) : M \is m.-s2int -> M^T* = M^T.
Proof.
move=> /mxs2intP H; apply/matrixP=> i j; rewrite !mxE.
rewrite conj_Creal //.
rewrite -[M j i](mulfK (sqrt2X_neq0 m)) rpredM //.
  by rewrite mulrC Creal_s2Int.
by rewrite rpredXN // Creal_s2Int // sQ2_proof.
Qed.

(* An element of M scaled by s2 ^ m is odd *) 
Definition mxodd {n} m :=
 [qualify M |
  [exists i, exists j, odds2i ((sqrtC 2%:R) ^+ m * (M : 'M_n) i j)]].

Notation " m .-odd" := (mxodd m) (format "m .-odd", at level 10).

Lemma mxodd1 n : (1 : 'M_n.+1) \is 0.-odd.
Proof.
apply/existsP; exists 0; apply/existsP; exists 0.
by rewrite mxE mulr1 (odds2i_nat 1).
Qed.

Lemma mxoddP n m (M : 'M_n) : 
  reflect (exists i, exists j, 
                   odds2i ((sqrtC 2%:R) ^+ m * M i j))
          (M \is m.-odd).
Proof.
apply: (iffP existsP) => [[i /existsP[j H]]|[i [j H]]].
  by exists i; exists j.
by exists i; apply/existsP; exists j.
Qed.

Lemma mxoddPn n m (M : 'M_n) : 
  reflect (forall i j, ~~ odds2i ((sqrtC 2%:R) ^+ m * M i j)) 
          (~~ (M \is m.-odd)).
Proof.
rewrite negb_exists.
apply: (iffP forallP) => [H i j|H i].
  by have := H i; rewrite negb_exists => /forallP/(_ j).
by rewrite negb_exists; apply/forallP.
Qed.

Lemma mxs2int_odd n m (M : 'M_n) :
  M \is m.+1.-s2int -> M \is m.-s2int =(M \isn't m.+1.-odd).
Proof.
move=> /mxs2intP H.
have [/mxoddP[i [j H1]]|/mxoddPn H1]/= := boolP (_ \is _.-odd).
  apply/negP=> /mxs2intP/(_ i j) H2.
  have := H1.
  by rewrite exprS -mulrA odds2iM  ?(negPf odds2i_sQ2) // sQ2_proof.
apply/mxs2intP=> i j.
have := H1 i j.
rewrite (odds2i_dvd (S2Iof (H i j))) => /dvdS2IP[r /val_eqP/eqP/=].
rewrite [RHS]mulrC exprS -!mulrA => /(mulfI sqrt2_neq0)->.
by apply: algS2IP.
Qed.

(* M is unitary and all the scaled elements are in s2Int *)
Definition mxsunitary {n} m :=
 [qualify M |  (M \is mxunitary) &&  ((M : 'M_n) \is m.-s2int)].

Notation " m .-sunitary" := (mxsunitary m) (format "m .-sunitary", at level 10).

Lemma mxsunitary_unitary n m (M : 'M_n) : M \is m.-sunitary -> M \is mxunitary.
Proof. by case/andP. Qed.

Lemma mxsunitary_s2int n m (M : 'M_n) i j : 
  M \is m.-sunitary -> (sqrtC 2%:R ^+ m) * M i j \is a s2Int.
Proof. by case/andP=> _ /mxs2intP. Qed.

Lemma mxsunitaryN n c (M : 'M_n) : M \is c.-sunitary -> -M \is c.-sunitary.
Proof.
move=> H.
have /andP[H1 /forallP H2] := H.
rewrite qualifE /mxsunitary ?mxunitaryN //.
apply/forallP=> i; apply/forallP=> j.
rewrite !mxE mulrN rpredN.
by have /forallP := H2 i.
Qed.

Lemma mxsunitaryM n m1 m2 (M1 M2 : 'M_n) : 
  M1 \is m1.-sunitary -> M2 \is m2.-sunitary -> 
  M1 *m M2 \is (m1 + m2).-sunitary.
Proof.
move=> /andP[H1o H1s] /andP[H2o H2s].
by rewrite qualifE /mxsunitary mxunitaryM // mxs2intM.
Qed.

Lemma mxsunitaryT n m (M : 'M_n) : (M ^T* \is m.-sunitary) = (M \is m.-sunitary).
Proof. by rewrite qualifE/mxsunitary mxs2intT mxunitaryT. Qed.

Lemma mxsunitary_inj k n (M M1 M2 : 'M_n) :
 M \is k.-sunitary ->  M *m M1 = M *m M2 -> M1 = M2.
Proof.
move=> Hs H.
have F : trCmx M *m M = 1%:M.
  have := Hs.
  rewrite -mxsunitaryT => /andP[].
  by rewrite qualifE /mxunitary trCmxK => /eqP.
by rewrite -[LHS]mul1mx -F -mulmxA H mulmxA F mul1mx.
Qed.
 
Lemma mxsunitary_tr n m (M : 'M_n) : M \is m.-sunitary -> M^T* = M^T.
Proof.
move=> sO.
apply/matrixP=> i j.
rewrite !mxE -{1}[M _ _](mulfK (sqrt2X_neq0 m)).
rewrite rmorphM !conj_Creal ?(mulfK (sqrt2X_neq0 m)) //.
  by rewrite rpredXN // Creal_s2Int // sQ2_proof.
by rewrite mulrC Creal_s2Int // (mxsunitary_s2int j i sO).
Qed.

Lemma mxsunitaryW n m1 m2  (M : 'M_n) : 
  (m1 <= m2)%N -> M \is m1.-sunitary -> M \is m2.-sunitary.
Proof.
by move=> H; rewrite !qualifE /mxsunitary => /andP[-> /(mxs2intW H)].
Qed.

Lemma mxsunitary0_odd n (M : 'M_n.+1) : M \is 0.-sunitary -> M \is 0.-odd.
Proof.
move=> Hn.
rewrite -[_ \is _]negbK negb_exists.
apply/negP=> /forallP /(_ 0).
rewrite negb_exists => /forallP H1.
have F i1 j1 : M i1 j1 \is a s2Int.
  by have /andP[_ /forallP/(_ i1)/forallP/(_ j1)] := Hn; rewrite mul1r.
have F1 : \sum_(k < n.+1) (M ord0 k) ^+ 2 = 1.
  have /mxunitaryP/(_ 0 0) := mxsunitary_unitary Hn.
  rewrite eqxx mulr1n => <-.
  apply: eq_bigr => k _.
  by rewrite expr2 conj_Creal // Creal_s2Int.
have : odds2i 1 by rewrite /odds2i (s2intA_nat 1).
rewrite -F1 odds2i_sum => [|i _ _]; last by rewrite rpredX.
rewrite big1 // => i _.
by have := negPf (H1 i); rewrite mul1r odds2iM // => ->.
Qed.

Lemma mxsunitary_odd n m (M : 'M_n) :
  M \is m.+1.-sunitary -> (M \is m.-sunitary) = (M \isn't m.+1.-odd).
Proof.
move=> /andP[Ho Hs].
by rewrite qualifE /mxsunitary Ho mxs2int_odd.
Qed.

Lemma mxoddN n c (M : 'M_n) : 
  M \is c.-sunitary -> (-M \is c.-odd) = (M \is c.-odd).
Proof.
move=> H.
apply/mxoddP/mxoddP; move=> [i [j Hij]]; exists i; exists j.
  rewrite !mxE mulrN in Hij.
  rewrite -odds2iN //.
  by apply: mxsunitary_s2int H.
by rewrite !mxE mulrN // odds2iN // (mxsunitary_s2int _ _ H).
Qed.

(* M is unitary and m is the smallest value such that all the scaled 
   elements are in s2Int *)
Definition mxounitary {n} m := 
 [qualify M |
  [&& (M : 'M_n) \is mxunitary, M \is m.-s2int & M \is m.-odd]].

Notation " m .-unitary" := (mxounitary m) (format "m .-unitary", at level 10).

Lemma mxounitaryE n m  (M : 'M_n) :
   (M \is m.-unitary) = ((M \is m.-sunitary) && (M \is m.-odd)).
Proof. by rewrite -andbA. Qed.

Lemma mxounitary_unitary n m (M : 'M_n) : M \is m.-unitary -> M \is mxunitary.
Proof. by case/and3P. Qed.

Lemma mxounitary_s2int n m (M : 'M_n) i j :
  M \is m.-unitary -> (sqrtC 2%:R ^+ m) * M i j \is a s2Int.
Proof. by case/and3P=> _ /mxs2intP. Qed.

Lemma mxounitary_sunitary n m (M : 'M_n) :
  M \is m.-unitary -> M \is m.-sunitary.
Proof. by rewrite mxounitaryE; case/andP. Qed.

Lemma mxounitary_odd n m (M : 'M_n) :
  M \is m.-unitary -> exists i, exists j, odds2i ((sqrtC 2%:R ^+ m) * M i j).
Proof. by case/and3P=> _ _ /mxoddP. Qed.

Lemma mxounitary1 n : (1 : 'M_n.+1) \is 0.-unitary.
Proof. by rewrite qualifE /mxounitary mxunitary1 mxs2int1 mxodd1. Qed.

Lemma mxounitaryN (n : nat) c (M : 'M_n) :
   M \is c.-unitary -> -M \is c.-unitary.
Proof.
move=> H; move: (H).
rewrite !mxounitaryE=> /andP[H1 H2].
by rewrite (mxoddN H1) mxsunitaryN.
Qed.

Lemma mxounitaryT n m (M : 'M_n) : (M ^T* \is m.-unitary) = (M \is m.-unitary).
Proof.
rewrite !mxounitaryE mxsunitaryT.
apply/andb_id2l=> /mxsunitary_s2int Hs.
apply/mxoddP/mxoddP => [] [i [j H1]]; exists j; exists i;
     have := H1; rewrite !mxE => H2.
  rewrite  -[_ * _]conjCK odds2i_conj ?s2Int_conj //.
  by rewrite rmorphM rmorphX conjC_sqrt2.
by rewrite -conjC_sqrt2 -rmorphX -rmorphM odds2i_conj.
Qed.

Lemma mxounitary_tr n m (M : 'M_n) : M \is m.-unitary -> M^T* = M^T.
Proof.
move=> sO.
have sn : M \is m.-sunitary by move: sO; rewrite mxounitaryE => /andP[]. 
by apply: mxsunitary_tr sn.
Qed.

Lemma odds2ij_row3 m (M : 'M_3) i (k := sqrtC (2%:R) ^+ m.+1) : 
  M \is m.+1.-sunitary -> 
   ~~ ((odds2i (k * M i 0) && odds2j (k * M i 0)) (+) 
       (odds2i (k * M i 1) && odds2j (k * M i 1)) (+) 
       (odds2i (k * M i o2) && odds2j (k * M i o2))).
Proof.
move=> /andP[/mxunitaryP/(_ i i)].
rewrite sum3E eqxx /= => H /mxs2intP F0.
have F1 j1 : 2%:R ^+ m.+1 *  (M i j1 * (M i j1)^*) =  (k * M i j1) ^+ 2.
  rewrite [RHS]expr2 -{2}(_ : k * (M i j1) ^* = k * M i j1).
    rewrite -[RHS]mulrA  [_ * (k * _)]mulrCA !mulrA -expr2.
    by rewrite -exprM mulnC exprM sqrtCK.
  rewrite {1}/k -conjC_sqrt2 -rmorphX -rmorphM.
  by rewrite conj_Creal // Creal_s2Int // s2Int_conj.
have : s2intB (2%:R ^+ m.+1 * 1%:R) == 0.
  by rewrite mulr1 -natrX /odds2j s2intB_nat.
rewrite -H !mulrDr !F1 !s2intB_add ?[s2intB (_ ^+ _)]s2intB_mul 
        ?(rpredX, rpredD) //.
have F2 x : x + x = 2%:R * x by rewrite mulrDl mul1r.
rewrite ![s2intB _ * _]mulrC !F2 -!mulrDr mulf_eq0 /=.
by rewrite /odds2i /odds2j /odds2j -!oddzM -!oddzD => /eqP->.
Qed.

Lemma odds2ij_col3 m (M : 'M_3) i (k := sqrtC (2%:R) ^+ m.+1)  : 
  M \is m.+1.-sunitary -> 
  ~~ ((odds2i (k * M 0 i) && odds2j (k * M 0 i)) (+) 
      (odds2i (k * M 1 i) && odds2j (k * M 1 i)) (+) 
      (odds2i (k * M o2 i) && odds2j (k * M o2 i))).
Proof.
move=> H.
move: (H); rewrite -mxsunitaryT  (mxsunitary_tr H) => H1.
have := odds2ij_row3 i H1.
by rewrite !mxE.
Qed.

Lemma odds2i_2row3 m (M : 'M_3) i j (k := sqrtC (2%:R) ^+ m.+1) : 
  M \is m.+1.-sunitary -> 
   ~~ ((odds2i (k * M i 0) && odds2i (k * M j 0)) (+) 
       (odds2i (k * M i 1) && odds2i (k * M j 1)) (+) 
       (odds2i (k * M i o2) && odds2i (k * M j o2))).
Proof.
move=> Hn.
have /mxsunitary_s2int Hs := Hn.
have /mxsunitary_unitary/mxunitaryP/(_ i j) := Hn.
rewrite sum3E => Ho.
have F1 j1 : 2%:R ^+ m.+1 *  (M i j1 * (M j j1)^*) = 
             (k * M i j1) * (k * M j j1).
  rewrite  -(_ : k * (M j j1) ^* = k * M j j1).
    rewrite -[RHS]mulrA  [_ * (k * _)]mulrCA !mulrA -expr2.
    by rewrite -exprM mulnC exprM sqrtCK.
  rewrite {1}/k -conjC_sqrt2 -rmorphX -rmorphM.
  by rewrite conj_Creal // Creal_s2Int // s2Int_conj.
have : ~~ odds2i (2%:R ^+ m.+1 * (i == j)%:R).
  case: eqP => _.
    rewrite mulr1.
    have ->: 2%:R ^+ m.+1 = (2%:R ^+ m.+1 : S2I) :> algC by rewrite rmorphX.
    rewrite odds2i_dvd; apply/dvdS2IP; exists (sQ2 * 2%:R ^+ m); rewrite exprSr.
    by rewrite mulrAC -expr2 sQ2K mulrC.
  by rewrite mulr0 /odds2i (s2intA_nat 0).
by rewrite -Ho !mulrDr !F1 !odds2iD ?rpredD 1?rpredM //
           ![odds2i (_ * _ * _)]odds2iM.
Qed.

Lemma odds2i_row3 m (M : 'M_3) i (k := sqrtC (2%:R) ^+ m.+1) : 
  M \is m.+1.-sunitary -> 
  ~~ (odds2i (k * M i 0) (+) odds2i (k * M i 1) (+) odds2i (k * M i o2)).
Proof.
move=> Hn.
have := odds2i_2row3 i i Hn.
by rewrite !andbb.
Qed.

Lemma odds2i_row3_gen m (M : 'M_3) i i1 j1 k1 (k := sqrtC (2%:R) ^+ m.+1)  : 
  M \is m.+1.-sunitary -> i1 != j1 -> i1 != k1 -> j1 != k1 ->
  ~~ (odds2i (k * M i i1) (+) odds2i (k * M i j1) (+) odds2i (k * M i k1)).
Proof.
move=> Hn i1Dj1 i1Dk1 j1Dk1.
rewrite (_ : _ (+) _ = \big[addb/false]_j (odds2i (k * M i j))); last first.
  rewrite (bigD1 i1) // (bigD1 j1) 1?eq_sym // 
          (bigD1 k1) ?[k1 == _]eq_sym ?i1Dk1 //=.
  rewrite big1 ?addbF ?addbA //.
  move=> k2 /andP[/andP[k2Di1 k2Dj1 k2Dk1]].
  have := card_ord 3.
  rewrite (cardD1 i1) (cardD1 j1) (cardD1 k1) (cardD1 k2).
  by rewrite !inE ![k1 == _]eq_sym i1Dk1 j1Dk1 k2Dk1 k2Dj1 k2Di1 eq_sym i1Dj1.
rewrite (bigD1 0) // (bigD1 1) // (bigD1 o2) //= big1 ?addbF ?addbA.
  by apply: odds2i_row3 Hn.
by case => [] [|[|[|]]].
Qed.

Lemma odds2i_2col3 m (M : 'M_3) i j (k := sqrtC (2%:R) ^+ m.+1) : 
  M \is m.+1.-sunitary -> 
   ~~ ((odds2i (k * M 0 i) && odds2i (k * M 0 j)) (+) 
       (odds2i (k * M 1 i) && odds2i (k * M 1 j)) (+) 
       (odds2i (k * M o2 i) && odds2i (k * M o2 j))).
Proof.
move=> H.
move: (H); rewrite -mxsunitaryT  (mxsunitary_tr H) => H1.
have := odds2i_2row3 i j H1.
by rewrite !mxE.
Qed.

Lemma odds2i_col3 m (M : 'M_3) i (k := sqrtC (2%:R) ^+ m.+1) : 
  M \is m.+1.-sunitary -> 
  ~~ (odds2i (k * M 0 i) (+) odds2i (k * M 1 i) (+) odds2i (k * M o2 i)).
Proof.
move=> Hn.
have := odds2i_2col3 i i Hn.
by rewrite !andbb.
Qed.

Lemma odds2i_col3_gen m (M : 'M_3) i i1 j1 k1 (k := sqrtC (2%:R) ^+ m.+1) : 
  M \is m.+1.-sunitary -> i1 != j1 -> i1 != k1 -> j1 != k1 ->
  ~~ (odds2i (k * M i1 i) (+) odds2i (k * M j1 i) (+) odds2i (k * M k1 i)).
Proof.
move=> Hn i1Dj1 i1Dk1 j1Dk1.
move: (Hn); rewrite -mxsunitaryT  (mxsunitary_tr Hn) => Hn1.
have := odds2i_row3_gen i Hn1 i1Dj1 i1Dk1 j1Dk1.
by rewrite !mxE.
Qed.

Lemma mxsunitary_eq0 (M : 'M_3) i j : 
  M \is 0.-sunitary -> [|| M i j == 0, M i j == -1 | M i j == 1].
Proof.
move=> Hn.
have F i1 j1 : M i1 j1 \is a s2Int.
  by have := mxsunitary_s2int i1 j1 Hn; rewrite mul1r.
have F1 : \sum_(k < 3) (M i k) ^+ 2 = 1.
  have /mxunitaryP/(_ i i) := mxsunitary_unitary Hn.
  rewrite eqxx mulr1n /= => <-.
  apply: eq_bigr => k _.
  by rewrite expr2 conj_Creal // Creal_s2Int.
have [/eqP->//|nZM]:= boolP (M i  j == 0).
have := congr1 s2intA F1.
rewrite (s2intA_nat 1) /= s2intA_sum /= => [|k _ _]; last first.
  by rewrite expr2 rpredM.
rewrite (bigD1 j) //= => H1.
suff /s2intA_sqrt_eq1-> : s2intA (M i j ^+ 2) = 1 by [].
apply: ler_anti.
rewrite -{1}[1]H1 ler_addl s2intA_sqrt_gt1 ?andbT //.
elim/big_rec: _ => // k y _ yP.
apply: addr_ge0 => //.
have [/eqP->|nZxs] := boolP (M i k == 0).
  by rewrite expr0n (s2intA_nat 0).
by apply: ler_trans (s2intA_sqrt_gt1  _ _).
Qed.

Definition even_row n m (M : 'M_n) i :=
   [forall j,  ~~ odds2i (((sqrtC 2%:R) ^+ m) * M i j)].

Lemma even_row3E i m (M : 'M_3) (k := (sqrtC 2%:R) ^+ m) : 
  even_row m M i = 
  [&& ~~ odds2i (k * M i 0), ~~ odds2i (k * M i 1)  &  ~~ odds2i (k * M i o2)].
Proof.
apply/forallP/and3P=> [H|[H1 H2 H3 j]] //.
by case/or3P: (o3E j) => /eqP->.
Qed. 

Lemma even_row3_inj i j m (M : 'M_3) :
  M \is m.+1.-unitary -> even_row m.+1 M i -> even_row m.+1 M j -> i = j.
Proof.
move=> Hs; move: (Hs).
rewrite mxounitaryE => /andP[Hn /mxoddP[i1 [j1 Ho1]]].
move=> /forallP/(_ j1) Ei /forallP/(_ j1) Ej.
case: (i =P j) => // /eqP iDj.
have i1Di : i1 != i by apply: contra Ei => /eqP<-.
have i1Dj : i1 != j by apply: contra Ej => /eqP<-.
have /negP[] := odds2i_col3_gen j1 Hn i1Di i1Dj iDj.
by rewrite Ho1 (negPf Ei) (negPf Ej).
Qed.

Definition even_col n m (M : 'M_n) j := 
   [forall i,  ~~ odds2i (((sqrtC 2%:R) ^+ m) * M i j)].

Lemma even_col_def n m (M : 'M_n) j : even_col m M j =  even_row m (M^T) j.
Proof.
by apply/forallP/forallP=> H i; have := H i; rewrite mxE.
Qed.

Lemma even_col_row n m (M : 'M_n) i : 
  M \is m.-s2int -> even_col m M i = even_row m (M^T*) i.
Proof. by move=> Hs; rewrite even_col_def (mxs2int_tr Hs). Qed.

Lemma even_row_col n m (M : 'M_n) i : even_row m M i = even_col m M^T i.
Proof. by rewrite even_col_def trmxK. Qed.

Lemma even_col3E i m M (k := (sqrtC 2%:R) ^+ m) : 
  even_col m M i = 
  [&& ~~ odds2i (k * M 0 i), ~~ odds2i (k * M 1 i) &  ~~ odds2i (k * M o2 i)].
Proof. by rewrite even_col_def even_row3E !mxE. Qed.

Lemma even_col3_inj i j m (M : 'M_3) :
  M \is m.+1.-unitary -> even_col m.+1 M i -> even_col m.+1 M j -> i = j.
Proof.
move=> Ho; rewrite !even_col_def; apply: even_row3_inj.
by rewrite -(mxounitary_tr Ho) mxounitaryT.
Qed.

Definition erow n m (M : 'M_n.+1) := odflt 0 [pick i | even_row m M i].
Definition ecol n m (M : 'M_n.+1) := odflt 0 [pick i | even_col m M i].

Lemma even_erow3 m (M : 'M_3) :
 M \is m.+1.-sunitary -> even_row m.+1 M (erow m.+1 M).
Proof.
move=> Hn; rewrite /erow; case: pickP => // H.
have := odds2i_row3 0 Hn.
have := odds2i_row3 1 Hn.
have := odds2i_row3 o2 Hn.
have :=  odds2i_2col3 0 1 Hn.
have :=  odds2i_2col3 0 o2 Hn.
have :=  odds2i_2col3 1 o2 Hn.
have /idP/negP := H 0.
have /idP/negP := H 1.
have /idP/negP := H o2.
rewrite !even_row3E.
by do 9 (case: odds2i; rewrite ?(addbT, addbF) //=).
Qed.

Lemma even_ecol3 m (M : 'M_3) :
  M \is m.+1.-sunitary -> even_col m.+1 M (ecol m.+1 M).
Proof.
move=> Hn; rewrite /ecol; case: pickP => // H.
have := odds2i_col3 0 Hn.
have := odds2i_col3 1 Hn.
have := odds2i_col3 o2 Hn.
have :=  odds2i_2row3 0 1 Hn.
have :=  odds2i_2row3 0 o2 Hn.
have :=  odds2i_2row3 1 o2 Hn.
have /idP/negP := H 0.
have /idP/negP := H 1.
have /idP/negP := H o2.
rewrite !even_col3E.
by do 9 (case: odds2i; rewrite ?(addbT, addbF) //=).
Qed.

Lemma mxounitary_odds2i m (M : 'M_3) i j (k := sqrtC (2%:R) ^+ m.+1)  :
  M \is m.+1.-unitary -> 
  odds2i (k * M i j) = (i != erow m.+1 M) && (j != ecol m.+1 M).
Proof.
move=> Hn.
move: Hn; rewrite mxounitaryE => /andP[Hn  /mxoddP[i1 [j1 Ho1]]].
case: eqP=> [->|/eqP Hr]/=.
  by have /forallP/(_ j)/negPf := even_erow3 Hn.
case: eqP=> [->|/eqP Hc]/=.
  by have /forallP/(_ i)/negPf := even_ecol3 Hn.
have iDe : i1 != erow m.+1 M.
  have /forallP/(_ j1) Hs1 := even_erow3 Hn.
  by apply: contra Hs1 => /eqP<-.
have jDe : j1 != ecol m.+1 M.
  have /forallP/(_ i1) Hs1 := even_ecol3 Hn.
  by apply: contra Hs1 => /eqP<-.
have [/eqP iEi1|iDi1] := boolP (i1 == i).
  have [/eqP jEj1|jDj1] := boolP (j1 == j).
    by rewrite -iEi1 -jEj1.
  have := odds2i_row3_gen i Hn jDj1 jDe Hc.
  rewrite (negPf (forallP (even_ecol3 Hn) i)) addbF.
  by rewrite -iEi1 Ho1 negbK.
have := odds2i_col3_gen j1 Hn iDi1 iDe Hr.
rewrite (negPf (forallP (even_erow3 Hn) j1)).
rewrite Ho1 addbF negbK => sO1.
have [/eqP <-//|jDj1] := boolP (j1 == j).
have := odds2i_row3_gen i Hn jDj1 jDe Hc.
by rewrite (negPf (forallP (even_ecol3 Hn) i)) sO1 addbF negbK.
Qed.

Lemma mxsunitary_oddij m k (M : 'M[algC]_3) :
   M \is m.+2.-sunitary ->  M \isn't m.+2.-odd ->
   (forall i j, j != k -> ~~ odds2j ((sqrtC 2%:R) ^+ m.+2 * M i j)) ->
   M \is m.-sunitary.
Proof.
move=> Hn Ho Hj.
have F1 : M \is m.+1.-sunitary by rewrite mxsunitary_odd.
have F2 (k1 : 'I_3)  : k1 != k -> even_col m.+1 M k1.
  move=> k1Dk; apply/forallP => i1.
  have F3 : ((sqrtC 2%:R)^m.+1 *: M) i1 k1 \is a s2Int.
    by have := mxsunitary_s2int i1 k1 F1; rewrite mxE.
  pose x := S2Iof F3.
  have F4 : ((sqrtC 2%:R)^m.+2 *: M) i1 k1 \is a s2Int
    by have := mxsunitary_s2int i1 k1 Hn; rewrite mxE.
  pose y := S2Iof F4.
  have yE : y = x * sQ2.
    apply/val_eqP => /=.
    by rewrite !mxE [_ * sqrtC _]mulrC mulrA.
  have := (odds2i_dvd x); rewrite /= mxE => ->.
  have oy : ~~ odds2i y.
    by have /mxoddPn /(_ i1 k1) := Ho; rewrite /= mxE.
  suff: 2%:R %| y.
    move=> /dvdS2IP[z]; rewrite yE -sQ2K expr2 mulrA.
    rewrite ![_ * sQ2]mulrC => HH.
    apply/dvdS2IP; exists z.
    have /mulfI : sQ2 != 0 by apply/val_eqP/eqP/sqrt2_neq0.
    apply.
    by rewrite HH [_ * z]mulrC.
  by rewrite -odds2ij_dvd negb_or oy /= !mxE Hj.
have /F2 H1 : k + 1 != k by rewrite addrC -subr_eq0 addrK.
have /F2 H2 : k + 2%:R != k by rewrite addrC -subr_eq0 addrK.
rewrite mxsunitary_odd //; apply/negP => Ho1.
suff /even_col3_inj/(_ H1 H2)/eqP : M \is m.+1.-unitary.
  by rewrite addrC -subr_eq0 opprD addrA addrK.
by rewrite mxounitaryE F1.
Qed.
  
Definition seq2matrix (R: ringType) m n (l: seq (seq R)) :=
  \matrix_(i<m,j<n) nth 1 (nth [::] l i) j.

Local Notation "''M{' l } " := (seq2matrix _ _ l).

Definition Tx :'M[algC]_3 := 
            (sqrtC 2%:R)^-1 *:  'M{[::[::sqrtC 2%:R; 0 ;  0]; 
                                   [::   0      ; 1 ; -1]; 
                                   [::   0      ; 1 ;  1]]}.

Lemma mxounitary_Tx : Tx \is 1.-unitary.
Proof.
have F := algS2IP sQ2.
have F1 : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
have F2 : (sqrtC 2%:R)^-1 \is Creal by rewrite rpredV Creal_s2Int.
apply/and3P; split.
- by apply/mxunitaryP => i j;
     case/or3P: (o3E i) => /eqP->; case/or3P: (o3E j) => /eqP->;
     rewrite sum3E !mxE
            ?(mulVf, conjC0, conjC1, mul0r, mulr0, addr0, add0r, mulr1, 
             mulrN1, mulNr, mulrN, opprK, rmorphN, subrr) //=;
    rewrite !conj_Creal // -invfM // -expr2 sqrtCK
             -[_^-1]mul1r -mulrDl mulfV // (eqC_nat 2 0).
- by apply/mxs2intP=> i j; 
     case/or3P : (o3E i) => /eqP->; case/or3P : (o3E j) => /eqP->;
     rewrite !mxE /= ?(mulr0, mulr1, mulrN, mulVf, mulfV)
                   ?(rpred0, rpredN, rpred1).
apply/mxoddP; exists 1; exists 1.
by rewrite !mxE /= mulr1 expr1 mulfV // (odds2i_nat 1).
Qed.

Definition Ty :'M[algC]_3 := 
             (sqrtC 2%:R)^-1 *: 'M{[::[:: 1 ;          0;  1]; 
                                   [:: 0 ; sqrtC 2%:R;  0]; 
                                   [::-1 ;          0;  1]]}.

Lemma mxounitary_Ty : Ty \is 1.-unitary.
Proof.
have F := algS2IP sQ2.
have F1 : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
have F2 : (sqrtC 2%:R)^-1 \is Creal by rewrite rpredV Creal_s2Int.
apply/andP; split.
  by apply/mxunitaryP => i j;
     case/or3P: (o3E i) => /eqP->; case/or3P: (o3E j) => /eqP->;
     rewrite sum3E !mxE
            ?(mulVf, conjC0, conjC1, mul0r, mulr0, addr0, add0r, mulr1, 
             mulrN1, mulNr, mulrN, opprK, rmorphN, oppr0) 1?addrC ?subrr //;
     rewrite !conj_Creal // -invfM // -expr2 sqrtCK
             -[_^-1]mul1r -mulrDl mulfV // (eqC_nat 2 0).
apply/andP; split.
  by apply/forallP=> i; apply/forallP=> j; 
     case/or3P : (o3E i) => /eqP->; case/or3P : (o3E j) => /eqP->;
     rewrite !mxE /= ?(mulr0, mulr1, mulrN, mulVf, mulfV)
                   ?(rpred0, rpredN, rpred1).
apply/existsP; exists 0; apply/existsP; exists 0.
by rewrite !mxE /= mulr1 expr1 mulfV // (odds2i_nat 1).
Qed.

Definition Tz :'M[algC]_3 := 
             (sqrtC 2%:R)^-1 *: 'M{[::[::1; -1;          0]; 
                                   [::1;  1;          0];
                                   [::0;  0; sqrtC 2%:R]]}.

Lemma mxounitary_Tz : Tz \is 1.-unitary.
Proof.
have F := algS2IP sQ2.
have F1 : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
have F2 : (sqrtC 2%:R)^-1 \is Creal by rewrite rpredV Creal_s2Int.
apply/andP; split.
  by apply/mxunitaryP => i j;
     case/or3P: (o3E i) => /eqP->; case/or3P: (o3E j) => /eqP->;
     rewrite sum3E !mxE
            ?(mulVf, conjC0, conjC1, mul0r, mulr0, addr0, add0r, mulr1, 
             mulrN1, mulNr, mulrN, opprK, rmorphN, oppr0) ?subrr //;
     rewrite !conj_Creal // -invfM // -expr2 sqrtCK
             -[_^-1]mul1r -mulrDl mulfV // (eqC_nat 2 0).
apply/andP; split.
  by apply/forallP=> i; apply/forallP=> j; 
     case/or3P : (o3E i) => /eqP->; case/or3P : (o3E j) => /eqP->;
     rewrite !mxE /= ?(mulr0, mulr1, mulrN, mulVf, mulfV)
                   ?(rpred0, rpredN, rpred1).
apply/existsP; exists 0; apply/existsP; exists 0.
by rewrite !mxE /= mulr1 expr1 mulfV // (odds2i_nat 1).
Qed.

Lemma TxT_mul (M : 'M[algC]_3) :
   Tx^T* * M =
 (sqrtC 2%:R)^-1 *:
 'M{[::[::sqrtC 2%:R * M 0 0; sqrtC 2%:R * M 0 1 ;  sqrtC 2%:R * M 0 o2]; 
       [::   M 1 0 + M o2 0;     M 1 1 + M o2 1;     M 1 o2 + M o2 o2];
       [:: - M 1 0 + M o2 0;   - M 1 1 + M o2 1;   - M 1 o2 + M o2 o2]]}.
Proof.
apply/matrixP=> i j.
have F := algS2IP sQ2.
have F1 : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
have F2 : (sqrtC 2%:R)^-1 \is Creal by rewrite rpredV Creal_s2Int.
rewrite !mxE sum3E !mxE /=.
by case/or3P: (o3E i) => /eqP->; case/or3P: (o3E j) => /eqP-> /=;
   rewrite ?(mulrA, mulVf, mul0r, mulr0, mul1r, mulr1, rmorph1, rmorph0, 
            add0r, addr0) //;
   rewrite ?(mulrN1, rmorphN, mulNr, (I, mulrN));
   rewrite  conj_Creal // ?Creal_s2Int // -mulrDr.
Qed.

Lemma TxT_mul_row  (M : 'M[algC]_3) i j :
   (Tx^T* * M) i j = if i == 0 then M 0 j
                   else if i == 1 then  (sqrtC 2%:R)^-1 * (M 1 j + M o2 j) else 
                   (sqrtC 2%:R)^-1 * (- M 1 j + M o2 j).
Proof.
have F1 : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
rewrite TxT_mul !mxE.
by case/or3P : (o3E i) => /eqP->; case/or3P : (o3E j) => /eqP->;
   rewrite //= mulrA mulVf ?mul1r.
Qed.

Lemma TyT_mul (M : 'M[algC]_3) :
   Ty^T* * M =
 (sqrtC 2%:R)^-1 *:
 'M{[::[::   M 0 0 - M o2 0;     M 0 1 - M o2 1;     M 0 o2 - M o2 o2];
       [::sqrtC 2%:R * M 1 0; sqrtC 2%:R * M 1 1 ;  sqrtC 2%:R * M 1 o2]; 
       [::   M 0 0 + M o2 0;     M 0 1 + M o2 1;     M 0 o2 + M o2 o2]]}.
Proof.
apply/matrixP=> i j.
have F := algS2IP sQ2.
have F1 : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
have F2 : (sqrtC 2%:R)^-1 \is Creal by rewrite rpredV Creal_s2Int.
rewrite !mxE sum3E !mxE /=.
by case/or3P: (o3E i) => /eqP->; case/or3P: (o3E j) => /eqP-> /=;
   rewrite ?(mulrA, mulVf, mul0r, mulr0, mul1r, mulr1, rmorph1, rmorph0, 
            add0r, addr0) //;
   rewrite ?(mulrN1, rmorphN, mulNr, (I, mulrN));
   rewrite  conj_Creal // ?Creal_s2Int // -mulrDr.
Qed.

Lemma TyT_mul_row  (M : 'M[algC]_3) i j :
   (Ty^T* * M) i j = if i == 1 then M 1 j
                   else if i == o2 then (sqrtC 2%:R)^-1 * (M 0 j + M o2 j) else 
                    (sqrtC 2%:R)^-1 * (M 0 j - M o2 j).
Proof.
have F1 : sqrtC 2%:R != 0 :> algC  by rewrite sqrtC_eq0 (eqC_nat _ 0).
rewrite TyT_mul !mxE.
by case/or3P : (o3E i) => /eqP->; case/or3P : (o3E j) => /eqP->;
   rewrite //= mulrA mulVf ?mul1r.
Qed.

Lemma TzT_mul (M : 'M[algC]_3) :
   Tz^T* * M =
 (sqrtC 2%:R)^-1 *:
 'M{[::[::   M 0 0 + M 1 0;     M 0 1 + M 1 1;     M 0 o2 + M 1 o2];
       [:: - M 0 0 + M 1 0;   - M 0 1 + M 1 1;   - M 0 o2 + M 1 o2];
       [::sqrtC 2%:R * M o2 0; sqrtC 2%:R * M o2 1 ;  sqrtC 2%:R * M o2 o2]]}.
Proof.
apply/matrixP=> i j.
have F := algS2IP sQ2.
have F1 : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
have F2 : (sqrtC 2%:R)^-1 \is Creal by rewrite rpredV Creal_s2Int.
rewrite !mxE sum3E !mxE /=.
by case/or3P: (o3E i) => /eqP->; case/or3P: (o3E j) => /eqP-> /=;
   rewrite ?(mulrA, mulVf, mul0r, mulr0, mul1r, mulr1, rmorph1, rmorph0, 
            add0r, addr0) //;
   rewrite ?(mulrN1, rmorphN, mulNr, (I, mulrN));
   rewrite  conj_Creal // ?Creal_s2Int // -mulrDr.
Qed.

Lemma TzT_mul_row  (M : 'M[algC]_3) i j :
   (Tz^T* * M) i j = if i == o2 then M o2 j
                   else if i == 0 then (sqrtC 2%:R)^-1 * (M 0 j + M 1 j) else 
                   (sqrtC 2%:R)^-1 * (- M 0 j + M 1 j).
Proof.
have F1 : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
rewrite TzT_mul !mxE.
by case/or3P : (o3E i) => /eqP->; case/or3P : (o3E j) => /eqP->;
   rewrite //= mulrA mulVf ?mul1r.
Qed.

Lemma mxsunitary_TxT m (M : 'M_3) : 
  M \is m.+1.-unitary -> (Tx^T* * M \is m.-sunitary) = (erow m.+1 M == 0).
Proof.
move=> Hos.
have Hn := mxounitary_sunitary Hos.
pose k : algC := (sqrtC 2%:R) ^+ m.+1.
pose l : algC := (sqrtC 2%:R) ^+ m.+2.
have F := algS2IP sQ2.
have F1 : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
have S1 := mxounitary_s2int _ _ Hos.
case: eqP => [E1|/eqP D1].
  have F2 (k1 : 'I_3)  : 
    k1 != ecol m.+1 M -> even_col m.+2 (Tx ^T* * M) k1.
    move=> k1Dk; apply/forallP => i1.
    rewrite TxT_mul_row.
    case: eqP => H1.
      rewrite exprS -mulrA odds2iM ?(algS2IP sQ2) // negb_and odds2i_sQ2.
      by rewrite (mxounitary_odds2i _ _ Hos).
    case: eqP => H2.
      rewrite exprSr !mulrA mulfK // mulrDr.
      rewrite odds2iD // negb_add.
      by rewrite !mxounitary_odds2i // E1.
    rewrite exprSr !mulrA mulfK // mulrDr mulrN.
    rewrite odds2iD ?rpredN // odds2iN // negb_add.
    by rewrite !mxounitary_odds2i // E1.
  have /F2 H1 : ecol m.+1 M + 1 != ecol m.+1 M.
    by rewrite addrC -subr_eq0 addrK.
  have /F2 H2 : ecol m.+1 M + 2%:R != ecol m.+1 M.
    by rewrite addrC -subr_eq0 addrK.
  have H3 : Tx ^T* * M \is m.+2.-sunitary.
    by rewrite -[m.+2]add1n mxsunitaryM //
               mxsunitaryT ?mxounitary_sunitary ?mxounitary_Tx.
  have F3 : Tx ^T* * M \isn't m.+2.-odd.
    apply/negP=> F3.
    have Hos2 : Tx ^T* * M \is m.+2.-unitary by rewrite mxounitaryE H3.
    have /eqP := even_col3_inj Hos2 H1 H2.
    by rewrite addrC -subr_eq0 opprD addrA addrK.
  suff F4 i1 j1 : j1 !=
     ecol m.+1 M -> ~~ odds2j (l * (Tx ^T* * M) i1 j1).
    by apply: mxsunitary_oddij F4.
  move=> j1De.
  rewrite TxT_mul_row.
  case: eqP => H1'.
    rewrite [l]exprS -mulrA odds2jM ?(algS2IP sQ2) //.
    rewrite  (negPf odds2i_sQ2) odds2j_sQ2 /=.
    by rewrite (mxounitary_odds2i _ _ Hos) // negb_and !negbK E1.
  case: eqP => H2'.
    rewrite [l]exprSr !mulrA mulfK // mulrDr odds2jD // .
    have := odds2ij_col3 j1 Hn.
    by rewrite !(mxounitary_odds2i _ _ Hos) E1 j1De.
  rewrite [l]exprSr !mulrA mulfK // mulrDr mulrN.
  rewrite odds2jD ?rpredN // odds2jN //.
  have := odds2ij_col3 j1 Hn.
  by rewrite !(mxounitary_odds2i _ _ Hos) // E1 j1De.
apply/idP => /andP[_ /forallP/(_ 0)/forallP/(_ (ecol m.+1 M + 1))].
rewrite  TxT_mul_row /= => /s2intP [a [b Hab]].
have : odds2i (k * M 0 (ecol m.+1 M + 1)).
  by rewrite (mxounitary_odds2i _ _ Hos) eq_sym D1 addrC -subr_eq0 addrK.
rewrite {1}[k]exprS -mulrA Hab odds2iM ?sqrt2_S2I //.
  by rewrite (negPf odds2i_sQ2).
by apply/s2intP; exists a; exists b.
Qed.

Lemma mxounitaryS_TxT m (M : 'M_3) :
   M \is m.+2.-unitary -> Tx^T* * M \isn't m.-sunitary.
Proof.
move=> Hos; apply/negP=> Hn1.
have F : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
have := mxsunitary_TxT  Hos.
case: eqP => [He /idP Hn| He /idP[]]; last first.
  by apply: mxsunitaryW Hn1.
pose k : algC := sqrtC 2%:R ^+ m.+2.
pose l : algC := sqrtC 2%:R ^+ m.+1.
pose l1 : algC := sqrtC 2%:R ^+ m.
pose x := l * ((Tx ^T* * M) 1 (ecol m.+2 M + 1)).
have Px : x \is a s2Int by apply: mxsunitary_s2int Hn.
have [Ox|Ex] := boolP (odds2i x).
  suff : sQ2 %| (S2Iof Px) by rewrite -odds2i_dvd Ox.
  pose x1 := l1 * ((Tx ^T* * M)  1 (ecol m.+2 M + 1)).
  have Px1 : x1 \is a s2Int by apply: mxsunitary_s2int Hn1.
  apply/dvdS2IP; exists (S2Iof Px1).
  apply/val_eqP => /=.
  by rewrite /x /x1 !mxE [_ * sqrtC _]mulrC mulrA [l]exprS.
pose y := l * ((Tx ^T* * M)) o2 (ecol m.+2 M + 1).
have Py : y \is a s2Int by apply: mxsunitary_s2int Hn.
have : odds2i (x + y).
  rewrite /x /y TxT_mul_row /= TxT_mul_row /=. 
  rewrite !mulrDr !mulrN [_ * _ + _]addrC addrA addrK -mulrDr.
  rewrite (_ : ?[x] + ?x = 2%:R * ?x); last by rewrite mulrDl mul1r.
  rewrite -{1}[2%:R]sqrtCK !mulrA -exprSr mulfK //.
  by rewrite (mxounitary_odds2i _  _ Hos) He /=  addrC -subr_eq0 addrK.
rewrite odds2iD // (negPf Ex) /= => Oy.
suff : sQ2 %| (S2Iof Py) by rewrite -odds2i_dvd Oy.
pose y1 := l1 * ((Tx ^T* * M)  o2 (ecol m.+2 M + 1)).
have Py1 : y1 \is a s2Int by apply: mxsunitary_s2int Hn1.
apply/dvdS2IP; exists (S2Iof Py1). 
apply/val_eqP => /=.
by rewrite /y /y1 [_ * sqrtC _]mulrC mulrA -exprS.
Qed.

Lemma mxsunitary_TyT m (M : 'M_3) : 
  M \is m.+1.-unitary -> (Ty^T* * M \is m.-sunitary) = (erow m.+1 M == 1).
Proof.
move=> Hos.
have Hn := mxounitary_sunitary Hos.
pose k : algC := (sqrtC 2%:R) ^+ m.+1.
pose l : algC := (sqrtC 2%:R) ^+ m.+2.
have F := algS2IP sQ2.
have F1 : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
have S1 := mxounitary_s2int _ _ Hos.
case: eqP => [E1|/eqP D1].
  have F2 (k1 : 'I_3)  : 
    k1 != ecol m.+1 M -> even_col m.+2 (Ty ^T* * M) k1.
    move=> k1Dk; apply/forallP => i1.
    rewrite TyT_mul_row.
    case: eqP => H1.
      rewrite exprS -mulrA odds2iM ?(algS2IP sQ2) // negb_and odds2i_sQ2.
      by rewrite (mxounitary_odds2i _ _ Hos).
    case: eqP => H2.
      rewrite exprSr !mulrA mulfK // mulrDr.
      rewrite odds2iD // negb_add.
      by rewrite !mxounitary_odds2i // E1.
    rewrite exprSr !mulrA mulfK // mulrDr mulrN.
    rewrite odds2iD ?rpredN // odds2iN // negb_add.
    by rewrite !mxounitary_odds2i // E1.
  have /F2 H1 : ecol m.+1 M + 1 != ecol m.+1 M.
    by rewrite addrC -subr_eq0 addrK.
  have /F2 H2 : ecol m.+1 M + 2%:R != ecol m.+1 M.
    by rewrite addrC -subr_eq0 addrK.
  have H3 : Ty ^T* * M \is m.+2.-sunitary.
    by rewrite -[m.+2]add1n mxsunitaryM //
               mxsunitaryT ?mxounitary_sunitary  ?mxounitary_Ty.
  have F3 : Ty ^T* * M \isn't m.+2.-odd.
    apply/negP=> F3.
    have Hos2 : Ty ^T* * M \is m.+2.-unitary by rewrite mxounitaryE H3.
    have /eqP := even_col3_inj Hos2 H1 H2.
    by rewrite addrC -subr_eq0 opprD addrA addrK.
  suff F4 i1 j1 : j1 !=
     ecol m.+1 M -> ~~ odds2j (l * (Ty ^T* * M) i1 j1).
    by apply: mxsunitary_oddij F4.
  move=> j1De.
  rewrite TyT_mul_row.
  case: eqP => H1'.
    rewrite [l]exprS -mulrA odds2jM ?(algS2IP sQ2) //.
    rewrite  (negPf odds2i_sQ2) odds2j_sQ2 /=.
    by rewrite (mxounitary_odds2i _ _ Hos) // negb_and !negbK E1.
  case: eqP => H2'.
    rewrite [l]exprSr !mulrA mulfK // mulrDr -/k odds2jD // .
    have := odds2ij_col3 j1 Hn.
    by rewrite !(mxounitary_odds2i _ _ Hos) // E1 j1De addbF.
  rewrite [l]exprSr !mulrA mulfK // mulrDr -/k mulrN.
  rewrite odds2jD ?rpredN // odds2jN //.
  have := odds2ij_col3 j1 Hn.
  by rewrite !(mxounitary_odds2i _ _ Hos) // E1 j1De addbF.
apply/idP => /andP[_ /forallP/(_ 1)/forallP/(_ (ecol m.+1 M + 1))].
rewrite  TyT_mul_row /= => /s2intP [a [b Hab]].
have : odds2i (k * M 1 (ecol m.+1 M + 1)).
  by rewrite (mxounitary_odds2i _ _ Hos) eq_sym D1 addrC -subr_eq0 addrK.
rewrite {1}[k]exprS -mulrA Hab odds2iM ?sqrt2_S2I //.
  by rewrite (negPf odds2i_sQ2).
by apply/s2intP; exists a; exists b.
Qed.


Lemma mxounitaryS_TyT m (M : 'M_3) :
   M \is m.+2.-unitary ->  Ty^T* * M \isn't m.-sunitary.
Proof.
move=> Hos; apply/negP=> Hn1.
have F : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
have := mxsunitary_TyT  Hos.
case: eqP => [He /idP Hn| He /idP[]]; last first.
  by apply: mxsunitaryW Hn1.
pose k : algC := sqrtC 2%:R ^+ m.+2.
pose l : algC := sqrtC 2%:R ^+ m.+1.
pose l1 : algC := sqrtC 2%:R ^+ m.
pose x := l * ((Ty ^T* * M) 0 (ecol m.+2 M + 1)).
have Px : x \is a s2Int by apply: mxsunitary_s2int Hn.
have [Ox|Ex] := boolP (odds2i x).
  suff : sQ2 %| (S2Iof Px) by rewrite -odds2i_dvd Ox.
  pose x1 := l1 * ((Ty ^T* * M) 0 (ecol m.+2 M + 1)).
  have Px1 : x1 \is a s2Int by apply: mxsunitary_s2int Hn1.
  apply/dvdS2IP; exists (S2Iof Px1).
  apply/val_eqP => /=.
  by rewrite /x /x1 !mxE [_ * sqrtC _]mulrC mulrA [l]exprS.
pose y := l * ((Ty ^T* * M)) o2 (ecol m.+2 M + 1).
have Py : y \is a s2Int by apply: mxsunitary_s2int Hn.
have : odds2i (x + y).
  rewrite /x /y TyT_mul_row /= TyT_mul_row /=. 
  rewrite mulrBr !mulrDr mulrN -/k [X in odds2i(_ + _ + X)]addrC.
  rewrite addrA subrK -mulrDr.
  rewrite (_ : ?[x] + ?x = 2%:R * ?x); last by rewrite mulrDl mul1r.
  rewrite -{1}[2%:R]sqrtCK !mulrA -exprSr mulfK //.
  by rewrite (mxounitary_odds2i _  _ Hos) He /=  addrC -subr_eq0 addrK.
rewrite odds2iD // (negPf Ex) /= => Oy.
suff : sQ2 %| (S2Iof Py) by rewrite -odds2i_dvd Oy.
pose y1 := l1 * ((Ty ^T* * M)  o2 (ecol m.+2 M + 1)).
have Py1 : y1 \is a s2Int by apply: mxsunitary_s2int Hn1.
apply/dvdS2IP; exists (S2Iof Py1). 
apply/val_eqP => /=.
by rewrite /y /y1 [_ * sqrtC _]mulrC mulrA -exprS.
Qed.

Lemma mxsunitary_TzT m (M : 'M_3) : 
  M \is m.+1.-unitary -> (Tz^T* * M \is m.-sunitary) = (erow m.+1 M == o2).
Proof.
move=> Hos.
have Hn := mxounitary_sunitary Hos.
pose k : algC := (sqrtC 2%:R) ^+ m.+1.
pose l : algC := (sqrtC 2%:R) ^+ m.+2.
have F := algS2IP sQ2.
have F1 : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
have S1 := mxounitary_s2int _ _ Hos.
case: eqP => [E1|/eqP D1].
  have F2 (k1 : 'I_3)  : 
    k1 != ecol m.+1 M -> even_col m.+2 (Tz ^T* * M) k1.
    move=> k1Dk; apply/forallP => i1.
    rewrite TzT_mul_row.
    case: eqP => H1.
      rewrite exprS -mulrA odds2iM ?(algS2IP sQ2) // negb_and odds2i_sQ2.
      by rewrite (mxounitary_odds2i _ _ Hos).
    case: eqP => H2.
      rewrite exprSr !mulrA mulfK // mulrDr -/k.
      rewrite odds2iD // negb_add.
      by rewrite !mxounitary_odds2i // E1.
    rewrite exprSr !mulrA mulfK // mulrDr -/k mulrN.
    rewrite odds2iD ?rpredN // odds2iN // negb_add.
    by rewrite !mxounitary_odds2i // E1.
  have /F2 H1 : ecol m.+1 M + 1 != ecol m.+1 M.
    by rewrite addrC -subr_eq0 addrK.
  have /F2 H2 : ecol m.+1 M + 2%:R != ecol m.+1 M.
    by rewrite addrC -subr_eq0 addrK.
  have H3 : Tz ^T* * M \is m.+2.-sunitary.
    by rewrite -[m.+2]add1n mxsunitaryM // 
               mxsunitaryT ?mxounitary_sunitary ?mxounitary_Tz.
  have F3 : Tz ^T* * M \isn't m.+2.-odd.
    apply/negP=> F3.
    have Hos2 : Tz ^T* * M \is m.+2.-unitary by rewrite mxounitaryE H3.
    have /eqP := even_col3_inj Hos2 H1 H2.
    by rewrite addrC -subr_eq0 opprD addrA addrK.
  suff F4 i1 j1 : j1 !=
     ecol m.+1 M -> ~~ odds2j (l * (Tz ^T* * M) i1 j1).
    by apply: mxsunitary_oddij F4.
  move=> j1De.
  rewrite TzT_mul_row.
  case: eqP => H1'.
    rewrite [l]exprS -mulrA odds2jM ?(algS2IP sQ2) //.
    rewrite  (negPf odds2i_sQ2) odds2j_sQ2 /=.
    by rewrite (mxounitary_odds2i _ _ Hos) // negb_and !negbK E1.
  case: eqP => H2'.
    rewrite [l]exprSr !mulrA mulfK // mulrDr -/k odds2jD // .
    have := odds2ij_col3 j1 Hn.
    by rewrite !(mxounitary_odds2i _ _ Hos) // E1 j1De addbF.
  rewrite [l]exprSr !mulrA mulfK // mulrDr -/k mulrN.
  rewrite odds2jD ?rpredN // odds2jN //.
  have := odds2ij_col3 j1 Hn.
  by rewrite !(mxounitary_odds2i _ _ Hos) // E1 j1De addbF.
apply/idP => /andP[_ /forallP/(_ o2)/forallP/(_ (ecol m.+1 M + 1))].
rewrite  TzT_mul_row /= => /s2intP [a [b Hab]].
have : odds2i (k * M o2 (ecol m.+1 M + 1)).
  by rewrite (mxounitary_odds2i _ _ Hos) eq_sym D1 addrC -subr_eq0 addrK.
rewrite {1}[k]exprS -mulrA Hab odds2iM ?sqrt2_S2I //.
  by rewrite (negPf odds2i_sQ2).
by apply/s2intP; exists a; exists b.
Qed.

Lemma mxounitaryS_TzT m (M : 'M_3) :
   M  \is m.+2.-unitary -> Tz^T* * M \isn't m.-sunitary.
Proof.
move=> Hos; apply/negP=> Hn1.
have F : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
have := mxsunitary_TzT  Hos.
case: eqP => [He /idP Hn| He /idP[]]; last first.
  by apply: mxsunitaryW Hn1.
pose k : algC := sqrtC 2%:R ^+ m.+2.
pose l : algC := sqrtC 2%:R ^+ m.+1.
pose l1 : algC := sqrtC 2%:R ^+ m.
pose x := l * ((Tz ^T* * M) 0 (ecol m.+2 M + 1)).
have Px : x \is a s2Int by apply: mxsunitary_s2int Hn.
have [Ox|Ex] := boolP (odds2i x).
  suff : sQ2 %| (S2Iof Px) by rewrite -odds2i_dvd Ox.
  pose x1 := l1 * ((Tz ^T* * M) 0 (ecol m.+2 M + 1)).
  have Px1 : x1 \is a s2Int by apply: mxsunitary_s2int Hn1.
  apply/dvdS2IP; exists (S2Iof Px1).
  apply/val_eqP => /=.
  by rewrite /x /x1 !mxE [_ * sqrtC _]mulrC mulrA [l]exprS.
pose y := l * ((Tz ^T* * M)) 1 (ecol m.+2 M + 1).
have Py : y \is a s2Int by apply: mxsunitary_s2int Hn.
have : odds2i (x + y).
  rewrite /x /y TzT_mul_row /= TzT_mul_row /=.
  rewrite !mulrDr !mulrN -/k [X in odds2i(X + _)]addrC.
  rewrite addrA addrK -mulrDr.
  rewrite (_ : ?[x] + ?x = 2%:R * ?x); last by rewrite mulrDl mul1r.
  rewrite -{1}[2%:R]sqrtCK !mulrA -exprSr mulfK //.
  by rewrite (mxounitary_odds2i _  _ Hos) He /=  addrC -subr_eq0 addrK.
rewrite odds2iD // (negPf Ex) /= => Oy.
suff : sQ2 %| (S2Iof Py) by rewrite -odds2i_dvd Oy.
pose y1 := l1 * ((Tz ^T* * M) 1 (ecol m.+2 M + 1)).
have Py1 : y1 \is a s2Int by apply: mxsunitary_s2int Hn1.
apply/dvdS2IP; exists (S2Iof Py1). 
apply/val_eqP => /=.
by rewrite /y /y1 [_ * sqrtC _]mulrC mulrA -exprS.
Qed.

Lemma Tx_mul (M : 'M[algC]_3) :
   Tx * M =
 (sqrtC 2%:R)^-1 *:
 'M{[::[::sqrtC 2%:R * M 0 0; sqrtC 2%:R * M 0 1 ;  sqrtC 2%:R * M 0 o2]; 
       [::   M 1 0 - M o2 0;     M 1 1 - M o2 1;     M 1 o2 - M o2 o2];
       [::   M 1 0 + M o2 0;     M 1 1 + M o2 1;     M 1 o2 + M o2 o2]]}.
Proof.
apply/matrixP=> i j.
have F : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
rewrite !mxE sum3E !mxE.
by case/or3P : (o3E i) => /eqP->; case/or3P : (o3E j) => /eqP-> /=;
   rewrite /= ?(mul0r, mulr0, mulr1, add0r, addr0, mulNr, mulrN, mul1r)
           ?mulrA ?mulVf // ?mulrBr ?mulrDr.
Qed.

Lemma Tx_mul_row  (M : 'M[algC]_3) i j :
   (Tx * M) i j = if i == 0 then M 0 j
                   else if i == 1 then  (sqrtC 2%:R)^-1 * (M 1 j - M o2 j) else 
                   (sqrtC 2%:R)^-1 * (M 1 j + M o2 j).
Proof.
rewrite Tx_mul !mxE.
have F : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
by case/or3P : (o3E i) => /eqP->; case/or3P : (o3E j) => /eqP->//=;
   rewrite mulrA mulVf // mul1r.
Qed.

Lemma mxsunitary0_neq0_row (M : 'M_3) i j k :
  M \is 0.-sunitary ->  M i j != 0 -> M i k = (k == j)%:R * M i k.
Proof.
have [|kDj Hs /negP Mij] := boolP (k == _); first by rewrite mul1r.
have /andP[/mxunitaryP /(_ i i)/eqP] := Hs.
rewrite sum3E -!addrA -!normCK eqxx mul0r.
have : `|M i j| = 1.
  by have /or3P[/eqP->//|/eqP->|/eqP->] := mxsunitary_eq0 i j Hs;
     rewrite ?normrN1 ?normr1 ?expr1n.
move: kDj.
case/or3P : (o3E j) => /eqP-> kDj ->; rewrite expr1n.
- rewrite -[1%:R]addr0.
  move/eqP/addrI/eqP.
  rewrite addr_ss_eq0 ?sqr_ge0 ?normr_ge0 //; last by rewrite !exprn_ge0.
  rewrite !sqrf_eq0 !normr_eq0 => /andP[/eqP H2 /eqP H3] _.
  move: kDj.
  by case/or3P : (o3E k) => /eqP->; rewrite ?eqxx.
- rewrite addrCA -[1%:R]addr0.
  move/eqP/addrI/eqP.
  rewrite addr_ss_eq0 ?sqr_ge0 ?normr_ge0 //; last by rewrite !exprn_ge0.
  rewrite !sqrf_eq0 !normr_eq0 => /andP[/eqP H2 /eqP H3] _.
  move: kDj.
  by case/or3P : (o3E k) => /eqP->; rewrite ?eqxx.
rewrite !addrA -[1%:R]add0r.
move/eqP/addIr/eqP.
rewrite addr_ss_eq0 ?sqr_ge0 ?normr_ge0 //; last by rewrite !exprn_ge0.
rewrite !sqrf_eq0 !normr_eq0 => /andP[/eqP H2 /eqP H3] _.
move: kDj.
by case/or3P : (o3E k) => /eqP->; rewrite ?eqxx.
Qed.

Lemma mxsunitary0_neq0_col (M : 'M_3) i j k : 
  M \is 0.-sunitary -> M i j != 0 -> M k j = (k == i)%:R * M k j.
Proof.
move=> Hn Mij; apply/eqP.
have [|kDj] := boolP (k == _); first by rewrite mul1r.
rewrite mul0r.
rewrite -mxsunitaryT in Hn.
have /(_ j i) := mxsunitary0_neq0_row k Hn.
rewrite !mxE (negPf kDj) mul0r conjC_eq0 => /(_ Mij)/eqP.
by rewrite conjC_eq0.
Qed.

Lemma mxsunitary0_neq0_odd (M : 'M_3) i j : 
  M \is 0.-sunitary -> M i j != 0 -> odds2i (M i j).
Proof.
move=> Hn /negP.
by have /or3P[//|/eqP->|/eqP->] := mxsunitary_eq0 i j Hn;
  rewrite ?odds2iN ?rpred1 // (odds2i_nat 1).
Qed. 

Lemma mxsunitary0_ex_neq0 (M : 'M_3) i :
  M \is 0.-sunitary -> exists j, M i j != 0.
Proof.
move=> Hn; apply/existsP.
have [//|] := boolP [exists x, M i x != 0].
rewrite negb_exists => /forallP H.
have H1 x : M i x = 0.
  by apply/eqP; rewrite -[_ == 0]negbK (negPf (H _)).  
have /andP[/mxunitaryP /(_ i i)/eqP] := Hn.
by rewrite sum3E !H1 !mul0r !add0r eqxx eq_sym oner_eq0.
Qed.

Lemma mxsunitary0_Tx_odd (M : 'M_3) : M \is 0.-sunitary -> Tx * M \is 1.-odd.
Proof.
move=> Hn; apply/mxoddP.
have F : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
have [i M1i] := mxsunitary0_ex_neq0 1 Hn.
exists 1; exists i.
rewrite Tx_mul_row /= mulrA mulfV // mul1r.
rewrite (mxsunitary0_neq0_col o2 Hn M1i) /=.
by rewrite mul0r subr0 mxsunitary0_neq0_odd.
Qed.

Lemma mxounitary_Tx_odd m (M : 'M_3) : 
  M \is m.+1.-unitary -> (Tx * M \is m.+2.-odd) = (erow m.+1 M != 0).
Proof.
move=> Hos.
have F : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
have Hs2i := mxounitary_s2int _ _ Hos.
have [eO1|dO1] /= := boolP (_ == _); apply/idP.
  apply/negP/mxoddPn => i j.
  rewrite Tx_mul_row /=.
  have := mxounitary_odds2i 1 j Hos.
  have := mxounitary_odds2i o2 j Hos.
  rewrite (eqP eO1) (negPf (_ : o2 != 0)) //= => H1 H2.
  have [/eqP iE|] := boolP (i == 0); last first.
    rewrite 2!fun_if !mulrA exprSr mulfK // !mulrDr mulrN.
    by rewrite !odds2iD ?odds2iN ?rpredN ?H1 ?H2 ?addbb ?if_same.
  by rewrite exprS -mulrA odds2iM ?(negPf odds2i_sQ2) ?sqrt2_S2I.
pose j := ecol m.+1 M + 1.
apply/mxoddP; exists o2; exists j.
rewrite Tx_mul_row /= exprSr !mulrA mulfK // mulrDr.
rewrite odds2iD // (mxounitary_odds2i 1 j Hos) 
                   (mxounitary_odds2i o2 j Hos) /j.
have := dO1.
by case/or3P : (o3E (erow m.+1 M)) => /eqP-> //;
   case/or3P : (o3E (ecol m.+1 M)) => /eqP->.
Qed.


Lemma mxounitary_Tx_sunitary m (M : 'M_3) :
  M \is m.+1.-unitary -> (Tx * M \is m.-sunitary) = (erow m.+1 M == 0).
Proof.
move=> Hos.
have F : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
set k : algC := (sqrtC 2%:R) ^+ m.+1.
set l : algC := (sqrtC 2%:R) ^+ m.+2.
have S1 := mxounitary_s2int _ _ Hos.
case: eqP => [E1|/eqP D1].
  have F1 (k1 : 'I_3)  : k1 != ecol m.+1 M -> even_col m.+2 (Tx * M) k1.
    move=> k1Dk; apply/forallP => i1.
    rewrite Tx_mul_row.
    case: eqP => H1.
      rewrite exprS -mulrA.
      rewrite odds2iM ?(algS2IP sQ2) // negb_and odds2i_sQ2.
      by rewrite (mxounitary_odds2i _ _ Hos).
    case: eqP => H2.
      rewrite exprSr mulrA mulfK // mulrBr.
      rewrite odds2iD ?rpredN // odds2iN // negb_add.
      by rewrite !(mxounitary_odds2i _ _ Hos) E1.
    rewrite exprSr mulrA mulfK // mulrDr.
    rewrite odds2iD // negb_add.
    by rewrite !(mxounitary_odds2i _ _ Hos) E1.
  have /F1 H1 : ecol m.+1 M + 1 != ecol m.+1 M.
    by rewrite addrC -subr_eq0 addrK.
  have /F1 H2 : ecol m.+1 M + 2%:R != ecol m.+1 M.
    by rewrite addrC -subr_eq0 addrK.
  have H3 : Tx * M \is m.+2.-sunitary.
    by rewrite -[m.+2]add1n mxsunitaryM // 
                mxounitary_sunitary // mxounitary_Tx.
  have F2 : Tx * M \isn't m.+2.-odd.
    apply/negP=> H.
    have /even_col3_inj/(_ H1 H2) /eqP : Tx * M \is m.+2.-unitary.
      by rewrite mxounitaryE H3.
    by rewrite addrC -subr_eq0 opprD addrA addrK.
  suff F3 i1 j1 : j1 != ecol m.+1 M -> ~~ odds2j (l * (Tx * M) i1 j1).
    by apply: mxsunitary_oddij F3.
  move=> j1De.
  rewrite Tx_mul_row.
  case: eqP => H1'.
    rewrite [l]exprS -mulrA.
    rewrite odds2jM ?(algS2IP sQ2) // (negPf odds2i_sQ2) odds2j_sQ2 /=.
    by rewrite (mxounitary_odds2i _ _ Hos) // negb_and !negbK E1.
  case: eqP => H2'.
    rewrite [l]exprSr mulrA mulfK // mulrBr.
    rewrite odds2jD ?odds2jN ?rpredN //.
    have := odds2ij_col3 j1 (mxounitary_sunitary Hos).
    by rewrite !(mxounitary_odds2i _ _ Hos) // E1 j1De.
  rewrite [l]exprSr mulrA mulfK // mulrDr.
  rewrite odds2jD //.
  have := odds2ij_col3 j1 (mxounitary_sunitary Hos).
  by rewrite !(mxounitary_odds2i _ _ Hos) // E1 j1De.
apply/idP => /andP[_ /forallP/(_ 0)/forallP/(_ (ecol m.+1 M + 1))].
rewrite  Tx_mul_row eqxx => /s2intP [a [b Hab]].
have : odds2i (k * M 0 (ecol m.+1 M + 1)).
  by rewrite (mxounitary_odds2i _ _ Hos) eq_sym D1 addrC -subr_eq0 addrK.
rewrite {1}[k]exprS -mulrA Hab odds2iM ?sqrt2_S2I //.
  by rewrite (negPf odds2i_sQ2).
by apply/s2intP; exists a; exists b.
Qed.

Lemma Ty_mul (M : 'M[algC]_3) :
   Ty * M =
 (sqrtC 2%:R)^-1 *:
 'M{[::[::   M 0 0 + M o2 0;     M 0 1 + M o2 1;     M 0 o2 + M o2 o2];
       [::sqrtC 2%:R * M 1 0; sqrtC 2%:R * M 1 1 ;  sqrtC 2%:R * M 1 o2]; 
       [::  - M 0 0 + M o2 0;   -M 0 1 + M o2 1;    -M 0 o2 + M o2 o2]]}.
Proof.
apply/matrixP=> i j.
have F : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
rewrite !mxE sum3E !mxE.
by case/or3P : (o3E i) => /eqP->; case/or3P : (o3E j) => /eqP-> /=;
   rewrite /= ?(mul0r, mulr0, mulr1, add0r, addr0, mulNr, mulrN, mul1r)
           ?mulrA ?mulVf // ?mulrBr ?mulrDr // mulrN.
Qed.

Lemma Ty_mul_row  (M : 'M[algC]_3) i j :
   (Ty * M) i j = if i == 1 then M 1 j
                  else if i == o2 then (sqrtC 2%:R)^-1 * (- M 0 j + M o2 j) else 
                   (sqrtC 2%:R)^-1  * (M 0 j + M o2 j).
Proof.
rewrite Ty_mul !mxE.
have F : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
by case/or3P : (o3E i) => /eqP->; case/or3P : (o3E j) => /eqP->//=;
   rewrite mulrA mulVf // mul1r.
Qed.

Lemma mxsunitary0_Ty_odd (M : 'M_3) : M \is 0.-sunitary -> Ty * M \is 1.-odd.
Proof.
move=> Hn; apply/mxoddP.
have F : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
have [i M1i] := mxsunitary0_ex_neq0 0 Hn.
exists 0; exists i.
rewrite Ty_mul_row /= mulrA mulfV // mul1r.
rewrite (mxsunitary0_neq0_col o2 Hn M1i) /=.
by rewrite mul0r addr0 mxsunitary0_neq0_odd.
Qed.

Lemma mxounitary_Ty_odd m (M : 'M_3) : 
  M \is m.+1.-unitary -> (Ty * M \is m.+2.-odd) = (erow m.+1 M != 1).
Proof.
move=> Hos.
have F : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
have Hs2i := mxounitary_s2int _ _ Hos.
have [eO1|dO1] /= := boolP (_ == _); apply/idP.
  apply/negP/mxoddPn => i j.
  rewrite Ty_mul_row /=.
  have := mxounitary_odds2i 0 j Hos.
  have := mxounitary_odds2i o2 j Hos.
  rewrite (eqP eO1) //= => H1 H2.
  have [/eqP iE|] := boolP (i == 1); last first.
    rewrite 2!fun_if !mulrA exprSr mulfK // !mulrDr mulrN.
    by rewrite !odds2iD ?odds2iN ?rpredN ?H1 ?H2 ?addbb ?if_same.
  by rewrite exprS -mulrA odds2iM ?(negPf odds2i_sQ2) ?sqrt2_S2I.
pose j := ecol m.+1 M + 1.
apply/mxoddP; exists o2; exists j.
rewrite Ty_mul_row /=.
rewrite exprSr !mulrA mulfK // mulrDr mulrN.
rewrite odds2iD ?rpredN // ?odds2iN // (mxounitary_odds2i 0 j Hos) 
                   (mxounitary_odds2i o2 j Hos) /j.
have := dO1.
by case/or3P : (o3E (erow m.+1 M)) => /eqP-> //;
   case/or3P : (o3E (ecol m.+1 M)) => /eqP->.
Qed.

Lemma mxounitary_Ty_sunitary m (M : 'M_3) :
  M \is m.+1.-unitary -> (Ty * M \is m.-sunitary) = (erow m.+1 M == 1).
Proof.
move=> Hos.
have F : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
set k : algC := (sqrtC 2%:R) ^+ m.+1.
set l : algC := (sqrtC 2%:R) ^+ m.+2.
have S1 := mxounitary_s2int _ _ Hos.
case: eqP => [E1|/eqP D1].
  have F1 (k1 : 'I_3)  : k1 != ecol m.+1 M -> even_col m.+2 (Ty * M) k1.
    move=> k1Dk; apply/forallP => i1.
    rewrite Ty_mul_row.
    case: eqP => H1.
      rewrite exprS -mulrA.
      rewrite odds2iM ?(algS2IP sQ2) // negb_and odds2i_sQ2.
      by rewrite (mxounitary_odds2i _ _ Hos).
    case: eqP => H2.
      rewrite exprSr mulrA mulfK // mulrDr mulrN.
      rewrite odds2iD ?rpredN // odds2iN // negb_add.
      by rewrite !(mxounitary_odds2i _ _ Hos) E1.
    rewrite exprSr mulrA mulfK // mulrDr.
    rewrite odds2iD // negb_add.
    by rewrite !(mxounitary_odds2i _ _ Hos) E1.
  have /F1 H1 : ecol m.+1 M + 1 != ecol m.+1 M.
    by rewrite addrC -subr_eq0 addrK.
  have /F1 H2 : ecol m.+1 M + 2%:R != ecol m.+1 M.
    by rewrite addrC -subr_eq0 addrK.
  have H3 : Ty * M \is m.+2.-sunitary.
    by rewrite -[m.+2]add1n mxsunitaryM //
               mxounitary_sunitary // mxounitary_Ty.
  have F2 : Ty * M \isn't m.+2.-odd.
    apply/negP=> H.
    have /even_col3_inj/(_ H1 H2) /eqP : Ty * M \is m.+2.-unitary.
      by rewrite mxounitaryE H3.
    by rewrite addrC -subr_eq0 opprD addrA addrK.
  suff F3 i1 j1 : j1 != ecol m.+1 M -> ~~ odds2j (l * (Ty * M) i1 j1).
    by apply: mxsunitary_oddij F3.
  move=> j1De.
  rewrite Ty_mul_row.
  case: eqP => H1'.
    rewrite [l]exprS -mulrA.
    rewrite odds2jM ?(algS2IP sQ2) // (negPf odds2i_sQ2) odds2j_sQ2 /=.
    by rewrite (mxounitary_odds2i _ _ Hos) // negb_and !negbK E1.
  case: eqP => H2'.
    rewrite [l]exprSr mulrA mulfK // mulrDr mulrN.
    rewrite odds2jD ?odds2jN ?rpredN //.
    have := odds2ij_col3 j1 (mxounitary_sunitary Hos).
    by rewrite !(mxounitary_odds2i _ _ Hos) // E1 j1De addbF.
  rewrite [l]exprSr mulrA mulfK // mulrDr.
  rewrite odds2jD //.
  have := odds2ij_col3 j1 (mxounitary_sunitary Hos).
  by rewrite !(mxounitary_odds2i _ _ Hos) // E1 j1De addbF.
apply/idP => /andP[_ /forallP/(_ 1)/forallP/(_ (ecol m.+1 M + 1))].
rewrite  Ty_mul_row eqxx => /s2intP [a [b Hab]].
have : odds2i (k * M 1 (ecol m.+1 M + 1)).
  by rewrite (mxounitary_odds2i _ _ Hos) eq_sym D1 addrC -subr_eq0 addrK.
rewrite {1}[k]exprS -mulrA Hab odds2iM ?sqrt2_S2I //.
  by rewrite (negPf odds2i_sQ2).
by apply/s2intP; exists a; exists b.
Qed.

Lemma Tz_mul (M : 'M[algC]_3) :
   Tz * M =
 (sqrtC 2%:R)^-1 *:
 'M{[::[::   M 0 0 - M 1 0;     M 0 1 - M 1 1;     M 0 o2 - M 1 o2];
       [::   M 0 0 + M 1 0;     M 0 1 + M 1 1;     M 0 o2 + M 1 o2];
       [::sqrtC 2%:R * M o2 0; sqrtC 2%:R * M o2 1 ;  sqrtC 2%:R * M o2 o2]]}.
Proof.
apply/matrixP=> i j.
have F : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
rewrite !mxE sum3E !mxE.
by case/or3P : (o3E i) => /eqP->; case/or3P : (o3E j) => /eqP-> /=;
   rewrite /= ?(mul0r, mulr0, mulr1, add0r, addr0, mulNr, mulrN, mul1r)
           ?mulrA ?mulVf // ?mulrBr ?mulrDr // mulrN.
Qed.

Lemma Tz_mul_row  (M : 'M[algC]_3) i j :
   (Tz * M) i j = if i == o2 then M o2 j
                  else if i == 0 then (sqrtC 2%:R)^-1 * (M 0 j - M 1 j) else 
                  (sqrtC 2%:R)^-1 * (M 0 j + M 1 j).
Proof.
rewrite Tz_mul !mxE.
have F : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
by case/or3P : (o3E i) => /eqP->; case/or3P : (o3E j) => /eqP->//=;
   rewrite mulrA mulVf // mul1r.
Qed.

Lemma mxsunitary0_Tz_odd  (M : 'M_3) : M \is 0.-sunitary -> Tz * M \is 1.-odd.
Proof.
move=> Hn; apply/mxoddP.
have F : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
have [i M1i] := mxsunitary0_ex_neq0 0 Hn.
exists 1; exists i.
rewrite Tz_mul_row /= mulrA mulfV // mul1r.
rewrite (mxsunitary0_neq0_col 1 Hn M1i) /=.
by rewrite mul0r addr0 mxsunitary0_neq0_odd.
Qed.

Lemma mxounitary_Tz_odd m (M : 'M_3) :
  M \is m.+1.-unitary -> (Tz * M \is m.+2.-odd) = (erow m.+1 M != o2).
Proof.
move=> Hos.
have F : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
have Hs2i := mxounitary_s2int _ _ Hos.
have [eO1|dO1] /= := boolP (_ == _); apply/idP.
  apply/negP/mxoddPn => i j.
  rewrite Tz_mul_row /=.
  have := mxounitary_odds2i 0 j Hos.
  have := mxounitary_odds2i 1 j Hos.
  rewrite (eqP eO1) //= => H1 H2.
  have [/eqP iE|] := boolP (i == o2); last first.
    rewrite 2!fun_if !mulrA exprSr mulfK // !mulrDr mulrN.
    by rewrite !odds2iD ?odds2iN ?rpredN ?H1 ?H2 ?addbb ?if_same.
  by rewrite exprS -mulrA odds2iM ?(negPf odds2i_sQ2) ?sqrt2_S2I.
pose j := ecol m.+1 M + 1.
apply/mxoddP; exists 0; exists j.
rewrite Tz_mul_row /=.
rewrite exprSr !mulrA mulfK // mulrDr mulrN.
rewrite odds2iD ?rpredN // ?odds2iN // (mxounitary_odds2i 0 j Hos) 
                   (mxounitary_odds2i 1 j Hos) /j.
have := dO1.
by case/or3P : (o3E (erow m.+1 M)) => /eqP-> //;
   case/or3P : (o3E (ecol m.+1 M)) => /eqP->.
Qed.

Lemma mxounitary_Tz_sunitary m (M : 'M_3) :
  M \is m.+1.-unitary -> (Tz * M \is m.-sunitary) = (erow m.+1 M == o2).
Proof.
move=> Hos.
have F : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
set k : algC := (sqrtC 2%:R) ^+ m.+1.
set l : algC := (sqrtC 2%:R) ^+ m.+2.
have S1 := mxounitary_s2int _ _ Hos.
case: eqP => [E1|/eqP D1].
  have F1 (k1 : 'I_3)  : k1 != ecol m.+1 M -> even_col m.+2 (Tz * M) k1.
    move=> k1Dk; apply/forallP => i1.
    rewrite Tz_mul_row.
    case: eqP => H1.
      rewrite exprS -mulrA.
      rewrite odds2iM ?(algS2IP sQ2) // negb_and odds2i_sQ2.
      by rewrite (mxounitary_odds2i _ _ Hos).
    case: eqP => H2.
      rewrite exprSr mulrA mulfK // mulrDr mulrN.
      rewrite odds2iD ?rpredN // odds2iN // negb_add.
      by rewrite !(mxounitary_odds2i _ _ Hos) E1.
    rewrite exprSr mulrA mulfK // mulrDr.
    rewrite odds2iD // negb_add.
    by rewrite !(mxounitary_odds2i _ _ Hos) E1.
  have /F1 H1 : ecol m.+1 M + 1 != ecol m.+1 M.
    by rewrite addrC -subr_eq0 addrK.
  have /F1 H2 : ecol m.+1 M + 2%:R != ecol m.+1 M.
    by rewrite addrC -subr_eq0 addrK.
  have H3 : Tz * M \is m.+2.-sunitary.
    by rewrite -[m.+2]add1n mxsunitaryM //
               mxounitary_sunitary // mxounitary_Tz.
  have F2 : Tz * M \isn't m.+2.-odd.
    apply/negP=> H.
    have /even_col3_inj/(_ H1 H2) /eqP : Tz * M \is m.+2.-unitary.
      by rewrite mxounitaryE H3.
    by rewrite addrC -subr_eq0 opprD addrA addrK.
  suff F3 i1 j1 : j1 != ecol m.+1 M -> ~~ odds2j (l * (Tz * M) i1 j1).
    by apply: mxsunitary_oddij F3.
  move=> j1De.
  rewrite Tz_mul_row.
  case: eqP => H1'.
    rewrite [l]exprS -mulrA.
    rewrite odds2jM ?(algS2IP sQ2) // (negPf odds2i_sQ2) odds2j_sQ2 /=.
    by rewrite (mxounitary_odds2i _ _ Hos) // negb_and !negbK E1.
  case: eqP => H2'.
    rewrite [l]exprSr mulrA mulfK // mulrDr mulrN.
    rewrite odds2jD ?odds2jN ?rpredN //.
    have := odds2ij_col3 j1 (mxounitary_sunitary Hos).
    by rewrite !(mxounitary_odds2i _ _ Hos) // E1 j1De addbF.
  rewrite [l]exprSr mulrA mulfK // mulrDr.
  rewrite odds2jD //.
  have := odds2ij_col3 j1 (mxounitary_sunitary Hos).
  by rewrite !(mxounitary_odds2i _ _ Hos) // E1 j1De addbF.
apply/idP => /andP[_ /forallP/(_ o2)/forallP/(_ (ecol m.+1 M + 1))].
rewrite  Tz_mul_row eqxx => /s2intP [a [b Hab]].
have : odds2i (k * M o2 (ecol m.+1 M + 1)).
  by rewrite (mxounitary_odds2i _ _ Hos) eq_sym D1 addrC -subr_eq0 addrK.
rewrite {1}[k]exprS -mulrA Hab odds2iM ?sqrt2_S2I //.
  by rewrite (negPf odds2i_sQ2).
by apply/s2intP; exists a; exists b.
Qed.

Lemma Tx_mul_Ty_neq m (M : 'M[algC]_3) : M \is m.-sunitary -> Tx * M != Ty * M.
Proof.
move=> /andP[/eqP H _]; apply: contra (_: Tx != Ty) => [/eqP H1|].
  by rewrite -[Tx]mulmx1 -H mulmxA [_ *m M]H1 -mulmxA H mulmx1.
apply/eqP=> /matrixP/(_ 0 o2)/eqP.
by rewrite !mxE mulr0 mulr1 eq_sym invr_eq0 sqrtC_eq0 (eqC_nat _ 0).
Qed.

Lemma Tx_mul_Tz_neq m (M : 'M[algC]_3) : M \is m.-sunitary -> Tx * M != Tz * M.
Proof.
move=> /andP[/eqP H _]; apply: contra (_: Tx != Tz) => [/eqP H1|].
  by rewrite -[Tx]mulmx1 -H mulmxA [_ *m M]H1 -mulmxA H mulmx1.
apply/eqP=> /matrixP/(_ 1 0)/eqP.
by rewrite !mxE  mulr0 mulr1 eq_sym invr_eq0 sqrtC_eq0 (eqC_nat _ 0).
Qed.

Lemma Ty_mul_Tz_neq m (M : 'M[algC]_3) : M \is m.-sunitary -> Ty * M != Tz * M.
Proof.
move=> /andP[/eqP H _]; apply: contra (_: Ty != Tz) => [/eqP H1|].
  by rewrite -[Ty]mulmx1 -H mulmxA [_ *m M]H1 -mulmxA H mulmx1.
apply/eqP=> /matrixP/(_ 1 0)/eqP.
by rewrite !mxE  mulr0 mulr1 eq_sym invr_eq0 sqrtC_eq0 (eqC_nat _ 0).
Qed.

Lemma even_row3_Tx_mul k (M : 'M[algC]_3) :
  M \is k.-sunitary -> even_row k.+1  (Tx * M) 0.
Proof.
move=> Hs.
have F : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
apply/forallP=> /= i; rewrite Tx_mul !mxE /=.
by case/or3P: (o3E i) => /eqP->//=;
   rewrite !mulrA divfK // exprS -mulrA;
   rewrite odds2iM ?negb_and ?odds2i_sQ2 //
          ?(mxsunitary_s2int _ _ Hs) // sQ2_proof.
Qed.

Lemma even_row3_Ty_mul k (M : 'M[algC]_3) :
 M \is k.-sunitary -> even_row k.+1  (Ty * M) 1.
Proof.
move=> Hs.
have F : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
apply/forallP=> /= i; rewrite Ty_mul !mxE /=.
by case/or3P: (o3E i) => /eqP->//=;
   rewrite !mulrA divfK // exprS -mulrA;
   rewrite odds2iM ?negb_and ?odds2i_sQ2 //
          ?(mxsunitary_s2int _ _ Hs) // sQ2_proof.
Qed.

Lemma even_row3_Tz_mul k (M : 'M[algC]_3) :
  M \is k.-sunitary -> even_row k.+1  (Tz * M) o2.
Proof.
move=> Hs.
have F : sqrtC 2%:R != 0 :> algC by rewrite sqrtC_eq0 (eqC_nat _ 0).
apply/forallP=> /= i; rewrite Tz_mul !mxE /=.
by case/or3P: (o3E i) => /eqP->//=;
   rewrite !mulrA divfK // exprS -mulrA;
   rewrite odds2iM ?negb_and ?odds2i_sQ2 //
          ?(mxsunitary_s2int _ _ Hs) // sQ2_proof.
Qed.

Lemma even_row3_erow (k : nat) i (M : 'M_3) :
   M \is k.+1.-unitary -> even_row k.+1 M i -> erow k.+1 M = i.
Proof.
move=> Hos HE.
apply: even_row3_inj HE => //.
by apply/even_erow3/mxounitary_sunitary.
Qed.

Definition getM m (M : 'M[algC]_3) :=
  tnth [tuple of [::Tx; Ty; Tz]] (erow m M).

Lemma getME m M : [|| getM m M == Tx, getM m M == Ty | getM m M == Tz].
Proof.
rewrite /getM; set j := erow m M.
by case/or3P : (o3E j) => /eqP->; rewrite  !(tnth_nth Tx) /= ?eqxx ?orbT.
Qed.
 
Definition reduceT m (M : 'M[algC]_3) := getM m M ^T* * M.

Fixpoint reduceTs n m M := 
  if n is n1.+1 then reduceTs n1 m.-1 (reduceT m M) else M.

Lemma reduceTsS n m M : reduceTs n.+1 m M = reduceTs n m.-1 (reduceT m M).
Proof. by []. Qed.

Lemma mxsunitary_reduceT m (M : 'M_3) : 
  M \is m.+1.-unitary -> reduceT m.+1 M \is m.-sunitary .
Proof.
move=>  Hos.
rewrite /reduceT /getM.
case/or3P : (o3E (erow m.+1 M))=> H; rewrite (eqP H) /=.
- by rewrite mxsunitary_TxT.
- by rewrite mxsunitary_TyT.
by rewrite mxsunitary_TzT.
Qed.

Lemma mxounitary_reduceT m (M : 'M_3) : 
  M \is m.+1.-unitary -> reduceT m.+1 M \is m.-unitary.
Proof.
move=> Hos.
have Hn := mxsunitary_reduceT Hos.
rewrite mxounitaryE Hn /=.
case: m Hn Hos => [Hn Hos|m Hn Hos].
  by rewrite mxsunitary0_odd.
rewrite -[_ \is _]negbK -(mxsunitary_odd Hn).
rewrite /reduceT /getM; set k := erow m.+2 M.
case/or3P : (o3E k) => H; rewrite (eqP H) !(tnth_nth Tx) /=.
- by rewrite mxounitaryS_TxT.
- by rewrite mxounitaryS_TyT.
by rewrite mxounitaryS_TzT.
Qed.

Lemma mxounitary_reduceTs_rec m n (M : 'M_3) : 
  M \is (m + n).-unitary -> reduceTs n (m + n) M \is m.-unitary.
Proof.
elim: n m M => [m M |n IH m M HO]; first by rewrite addn0.
by rewrite addnS /= IH // mxounitary_reduceT // -addnS.
Qed.

Lemma mxounitary_reduceTs m (M : 'M_3) : 
  M \is m.-unitary -> reduceTs m m M \is 0.-unitary.
Proof. by rewrite {1 3} [m]/(0 + m)%N => /mxounitary_reduceTs_rec. Qed.

Lemma mxounitary0_Tx (M : 'M_3) : M \is 0.-unitary -> Tx * M \is 1.-unitary.
Proof.
move=> Hos; have Hn := mxounitary_sunitary Hos.
rewrite mxounitaryE mxsunitary0_Tx_odd ?andbT //.
by rewrite  (@mxsunitaryM _ 1 0) // mxounitary_sunitary // mxounitary_Tx.
Qed.

Lemma mxounitary_Tx_mul m (M : 'M_3) :
  M \is m.+1.-unitary -> Tx * M \is m.+2.-unitary = (erow m.+1  M != 0).
Proof.
move=> Hos; have Hn := mxounitary_sunitary Hos.
rewrite mxounitaryE mxounitary_Tx_odd // (@mxsunitaryM _ 1 m.+1) //.
by rewrite mxounitary_sunitary // mxounitary_Tx.
Qed.

Lemma mxounitary0_Ty (M : 'M_3) : M \is 0.-unitary -> Ty * M \is 1.-unitary.
Proof.
move=> Hos; have Hn := mxounitary_sunitary Hos.
rewrite mxounitaryE mxsunitary0_Ty_odd ?andbT //.
by rewrite  (@mxsunitaryM _ 1 0) // mxounitary_sunitary // mxounitary_Ty.
Qed.

Lemma mxounitary_Ty_mul m (M : 'M_3) : 
  M \is m.+1.-unitary -> Ty * M \is m.+2.-unitary = (erow m.+1  M != 1).
Proof.
move=> Hos; have Hn := mxounitary_sunitary Hos.
rewrite mxounitaryE mxounitary_Ty_odd // (@mxsunitaryM _ 1 m.+1) //.
by rewrite mxounitary_sunitary // mxounitary_Ty.
Qed.

Lemma mxounitary0_Tz (M : 'M_3) : M \is 0.-unitary -> Tz * M \is 1.-unitary.
Proof.
move=> Hos; have Hn := mxounitary_sunitary Hos.
rewrite mxounitaryE mxsunitary0_Tz_odd ?andbT //.
by rewrite  (@mxsunitaryM _ 1 0) // mxounitary_sunitary // mxounitary_Tz.
Qed.

Lemma mxounitary_Tz_mul m (M : 'M_3) : 
  M \is m.+1.-unitary -> Tz * M \is m.+2.-unitary = (erow m.+1  M != o2).
Proof.
move=> Hos; have Hn := mxounitary_sunitary Hos.
rewrite mxounitaryE mxounitary_Tz_odd // (@mxsunitaryM _ 1 m.+1) //.
by rewrite mxounitary_sunitary // mxounitary_Tz.
Qed.

Lemma erow_Tx0 M : M \is 0.-unitary -> erow 1 (Tx * M) = 0.
Proof.
move=> HM.
have F := mxounitary0_Tx HM.
move: (F); rewrite mxounitaryE => /andP[/even_erow3 F1 _].
apply: even_row3_erow F _.
apply/forallP => x.
rewrite expr1 Tx_mul_row eqxx //.
have F2 i1 j1 : M i1 j1 \is a s2Int.
  by have := (mxounitary_s2int i1 j1 HM); rewrite mul1r.
rewrite odds2iM  ? sQ2_proof ?(mxsunitary_s2int _ _ HM) //.
by rewrite ?negb_and ?odds2i_sQ2.
Qed.

Lemma erow_Tx k M : 
  M \is k.+1.-unitary -> erow k.+1 M != 0 -> erow k.+2 (Tx * M) = 0.
Proof.
move=> HM H.
have F : Tx * M \is k.+2.-unitary by rewrite mxounitary_Tx_mul.
move: (F); rewrite mxounitaryE => /andP[/even_erow3 F1 _].
apply: even_row3_erow F _.
apply/forallP => x.
rewrite Tx_mul_row eqxx exprS -mulrA.
rewrite odds2iM  ?sQ2_proof //.
  by rewrite ?negb_and ?odds2i_sQ2.
by exact: (mxounitary_s2int _ _ HM).
Qed.

Lemma erow_Ty0 M : M \is 0.-unitary -> erow 1 (Ty * M) = 1.
Proof.
move=> HM.
have F := mxounitary0_Ty HM.
move: (F); rewrite mxounitaryE => /andP[/even_erow3 F1 _].
apply: even_row3_erow F _.
apply/forallP => x.
rewrite expr1 Ty_mul_row eqxx //.
have F2 i1 j1 : M i1 j1 \is a s2Int.
  by have := (mxounitary_s2int i1 j1 HM); rewrite mul1r.
rewrite odds2iM  ? sQ2_proof ?(mxsunitary_s2int _ _ HM) //.
by rewrite ?negb_and ?odds2i_sQ2.
Qed.

Lemma erow_Ty k M : 
  M \is k.+1.-unitary -> erow k.+1 M != 1 -> erow k.+2 (Ty * M) = 1.
Proof.
move=> HM H.
have F : Ty * M \is k.+2.-unitary by rewrite mxounitary_Ty_mul.
move: (F); rewrite mxounitaryE => /andP[/even_erow3 F1 _].
apply: even_row3_erow F _.
apply/forallP => x.
rewrite Ty_mul_row eqxx exprS -mulrA.
rewrite odds2iM  ?sQ2_proof //.
  by rewrite ?negb_and ?odds2i_sQ2.
by exact: (mxounitary_s2int _ _ HM).
Qed.

Lemma erow_Tz0 M : M \is 0.-unitary -> erow 1 (Tz * M) = o2.
Proof.
move=> HM.
have F := mxounitary0_Tz HM.
move: (F); rewrite mxounitaryE => /andP[/even_erow3 F1 _].
apply: even_row3_erow F _.
apply/forallP => x.
rewrite expr1 Tz_mul_row eqxx //.
have F2 i1 j1 : M i1 j1 \is a s2Int.
  by have := (mxounitary_s2int i1 j1 HM); rewrite mul1r.
rewrite odds2iM  ? sQ2_proof ?(mxsunitary_s2int _ _ HM) //.
by rewrite ?negb_and ?odds2i_sQ2.
Qed.

Lemma erow_Tz k M : 
  M \is k.+1.-unitary -> erow k.+1 M != o2 -> erow k.+2 (Tz * M) = o2.
Proof.
move=> HM H.
have F : Tz * M \is k.+2.-unitary by rewrite mxounitary_Tz_mul.
move: (F); rewrite mxounitaryE => /andP[/even_erow3 F1 _].
apply: even_row3_erow F _.
apply/forallP => x.
rewrite Tz_mul_row eqxx exprS -mulrA.
rewrite odds2iM  ?sQ2_proof //.
  by rewrite ?negb_and ?odds2i_sQ2.
by exact: (mxounitary_s2int _ _ HM).
Qed.

Fixpoint Tn n : 'M_3 := 
  if n is n1.+1 then (if erow n1  (Tn n1) == 0 then Ty else Tx) * Tn n1
  else 1.

Lemma mxounitary_Tn k : Tn k \is k.-unitary.
Proof.
elim: k => [|k IH] /=; first by apply: mxounitary1.
case: k IH => [_ /=|k IH].
  rewrite mulr1; case (_ == _).
    by rewrite -[Ty]mulr1 mxounitary0_Ty // mxounitary1.
  by rewrite -[Tx]mulr1 mxounitary0_Tx // mxounitary1.
have [/eqP HE|HD] := boolP (_ == _).
  by rewrite mxounitary_Ty_mul // HE.
by rewrite mxounitary_Tx_mul // HE.
Qed.

End Quantum.

Notation "M ^T*" := (trCmx M) (at level 10).

Notation " m .-s2int" := (mxs2int m) (format "m .-s2int", at level 10).

Notation " m .-odd" := (mxodd m) (format "m .-odd", at level 10).

Notation " m .-sunitary" := (mxsunitary m) (format "m .-sunitary", at level 10).

Notation " m .-unitary" := (mxounitary m) (format "m .-unitary", at level 10).

Notation "''M{' l } " := (seq2matrix _ _ l).



