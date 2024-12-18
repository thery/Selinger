From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_field archimedean.
Require Import gauss_int.

(*****************************************************************************)
(*                                                                           *)
(*                                                                           *)
(*          Definition of the subtype a + b * sqrt(2) in algC                *)
(*                                                                           *)
(*                                                                           *)
(*****************************************************************************)
 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Open Scope ring_scope.

Section S2int.

Definition s2intA (x : algC) : int :=
  let p := minCpoly x in
    if size p == 3%N then
    let a :=  - (p`_ 1 / 2%:R) in Num.floor a else Num.floor x.

Definition s2intB (x : algC) : int :=
  let a := s2intA x in
  let b := sqrtC ((x - a%:~R) ^+2  / 2%:R) in
  (-1) ^+ (x - a%:~R < 0)%R * Num.floor b.

Definition s2Int_subdef : pred algC :=
  [pred x | x == (s2intA x)%:~R + (s2intB x)%:~R * sqrtC 2%:R].

Definition s2Int := [qualify a x : algC | s2Int_subdef x].

Lemma s2IntE x : 
  (x \is a s2Int) = (x == (s2intA x)%:~R + (s2intB x)%:~R * sqrtC 2%:R).
Proof. by []. Qed.

Lemma Creal_s2Int : {subset s2Int <= Num.real}.
Proof.
move=> x.
rewrite s2IntE => /eqP->.
rewrite rpredD // -[_ \in _]/(_ \is Num.real) ?rpredM //
        -[_ \in _]/(_ \is Num.real).
- by apply/Rreal_int/intr_int.
- by apply/Rreal_int/intr_int.
by rewrite qualifE /= sqrtC_ge0 (ler_nat _ 0).
Qed.

Lemma nat_irr2 m n : coprime m n -> (m ^ 2 != 2 * n ^ 2)%N.
Proof.
move=> Cp; apply/eqP=> m2E.
have : ~~ odd (m ^ 2) by rewrite m2E oddM.
rewrite oddX /= => Om.
have : ~~ odd (n ^ 2).
  have/eqP := m2E.
  rewrite -[m]odd_double_half (negPf Om) add0n.
  rewrite expnS expn1 -mul2n -mulnA eqn_mul2l => /eqP<-.
  by rewrite mulnCA oddM.
rewrite oddX /= => On.
suff /negP[] : ~~ (2 %| n)%N by rewrite dvdn2.
by rewrite -prime_coprime // (coprime_dvdl _ Cp) // dvdn2.
Qed.

Lemma nat_irr2E m n : ((m ^ 2 == 2 * n ^ 2) = ((m == 0) && (n == 0)))%N.
Proof.
apply/eqP/idP=> [|/andP[/eqP->/eqP->]//].
case: m; case: n => // n m H.
have /dvdnP[m1 Hm1] := dvdn_gcdl m.+1 n.+1.
have /dvdnP[n1 Hn1] := dvdn_gcdr m.+1 n.+1.
have Pg : (0 < gcdn m.+1 n.+1)%N by rewrite gcdn_gt0.
have /nat_irr2/eqP[]: coprime m1 n1.
  by rewrite /coprime -(eqn_pmul2r Pg)muln_gcdl -Hm1 -Hn1 mul1n.
apply/eqP; rewrite -sqrn_gt0 in Pg.
by rewrite -(eqn_pmul2r Pg) -mulnA -!expnMn -Hm1 -Hn1 H.
Qed.

Lemma int_irr2E (m n : int) : ((m ^ 2 == 2%:R * n ^ 2) = ((m == 0) && (n == 0))).
Proof.
apply/eqP/idP=> [H|/andP[/eqP->/eqP->]//].
suff : (`|m| ^ 2 == 2 * `|n| ^ 2)%N by rewrite nat_irr2E !absz_eq0.
by rewrite -!abszX [_ ^+ _]H -{3}(absz_nat 2) -abszM.
Qed.

Lemma rat_irr2 (r : rat) : r ^+ 2 != 2%:R.
Proof.
have /nat_irr2:= coprime_num_den r.
apply: contra => H.
rewrite -eqz_nat -(eqr_int (Num.NumDomain.clone _ rat)) /=.
rewrite !PoszM -!expr2 /= [X in _ == X]rmorphM /= -[2%:~R](eqP H).
rewrite -{2}[r]divq_num_den exprMn [X in _ == _ * X * _]exprVn.
rewrite !rmorphXn /= !abszE !intr_norm !real_normK ?realz //.
by rewrite mulfVK // expf_eq0 /= intq_eq0 denq_neq0.
Qed.

Lemma s2intP (x : algC) : 
  reflect (exists a, exists b, x = a%:~R + b%:~R * sqrtC 2%:R)
           (x \is a s2Int).
Proof.
rewrite s2IntE; apply: (iffP eqP) => [->|[a [b Eab]]].
  by exists (s2intA x); exists (s2intB x).
pose ar := ratz a; pose br := ratz b.
pose lp := [::- (2%:R * (br ^+ 2) - ar^+2);  - (2%:R * ar); 1].
pose p := Poly lp.
have sP : size p = 3%N. by rewrite [X in size X](@PolyK _ 0).
have rE : root (map_poly ratr p) x.
  rewrite map_polyE /root horner_Poly (@PolyK _ 0) //= mul0r add0r.
  rewrite rmorph1 mul1r raddfN /= rmorphM /=.
  rewrite ratr_nat [ar]ratzE ratr_int.
  rewrite raddfN raddfB /= rmorphM /= ratr_nat !rmorphXn /=.
  rewrite [br]ratzE !ratr_int.
  (* this should be ring *) 
  rewrite Eab !(mulNr, opprD, mulrDr, mulrDl) !mul1r !mulrA.
  rewrite ![_ * sqrtC _]mulrC !mulrA opprK !addrA -!expr2 sqrtCK.
  rewrite [_ * b%:~R * _]mulrAC.
  set x1 := _ ^+ _; set x2 := _ * _ * _.
  rewrite !mulrDl mul1r !(addrA, opprD) -expr2.
  set x3 := _ ^+ _.
  rewrite addrC !addrA.
  do 3 rewrite -[_ - ?[n] - ?n]addrA -opprD.
  rewrite [x1 + _ + x2]addrC addrK.
  by rewrite -[_ + x3]addrA [_ + (x3 + _)]addrC !addrK subrr.
suff gAE : s2intA x = a.
  suff -> : s2intB x = b by rewrite gAE.
  rewrite /s2intB gAE Eab -[a%:~R + _ ]addrC addrK.
  rewrite exprMn sqrtCK mulfK ?(eqr_nat _ _ 0) // pmulr_llt0; last first.
    by rewrite sqrtC_gt0 (ltr_nat _ 0).
  rewrite (ltr_int _ _ 0).
  case: (lerP 0 b) => [H|/ltW H].
  rewrite mul1r sqrCK ?intrKfloor // (ler_int _ 0) //=.
  rewrite mulNr mul1r -[_%:~R]opprK exprNn -signr_odd mul1r sqrCK ?oppr_ge0 //.
    by rewrite floorN  ?intr_int // opprK ?intrKfloor // (ler_int _ 0).
  by rewrite (ler_int _ _ 0).
rewrite /s2intA.
case: (minCpolyP x) (size_minCpoly x) (root_minCpoly x) rE
     => /= q [-> qM /(_ p) ->].
rewrite size_map_poly leq_eqVlt eq_sym => /orP[/eqP sZ H1 H2|H1 H2].
  rewrite sZ /=.
  move: H1.
  rewrite -[q]coefK sZ  poly_def 2!big_ord_recl big_ord0 addr0.
  set u := _ `_ _;   set v := _ `_ _.
  rewrite raddfD /= !map_polyZ /= !map_polyX expr0 ?expr1.
  move: qM.
  rewrite qualifE /= lead_coefE sZ -/v => /eqP->.
  rewrite !rmorph1 scale1r Eab /root !hornerE /=.
  have [/eqP-> _|nZb] := boolP (b == 0).
    by rewrite mul0r addr0 intrKfloor.
  rewrite addr_eq0 => /eqP HH.
  have /eqP[] := rat_irr2  ((u + a%:~R) / b%:~R).
  rewrite -[LHS]ratCK rmorphXn rmorphM /= rmorphD /= ratr_int // HH.
  rewrite mulNr exprNn -signr_odd mul1r [ratr _]rmorphV /=; last first.
    by rewrite unitfE (eqr_int _ _ 0).
  rewrite ratr_int [_%:~R * _]mulrC mulfK ?(eqr_int _ _ 0) //.
  by rewrite sqrtCK -[2%:R]ratr_nat ratCK.
move=> H3.
have : (size q <= size p)%N by rewrite dvdp_leq // -size_poly_eq0 sP.
rewrite sP => H4. 
rewrite eqn_leq H4 H1.
have /eqP<- : p == q.
  rewrite eq_sym -eqp_monic // -1?dvdp_size_eqp //.
    by rewrite sP eqn_leq H4 H1.
  by rewrite qualifE /= lead_coefE (@PolyK _ 0).
have -> : (map_poly ratr p)`_1 = ratr (- (2%:R * ar)) :> algC.
  by rewrite coef_map_id0 ?raddf0 // (@PolyK _ 0).
rewrite raddfN /= mulNr opprK rmorphM /= ratr_nat.
rewrite [2%:R * _]mulrC mulfK ?(eqC_nat _ 0) //.
by rewrite [ar]ratzE ratr_int intrKfloor.
Qed.

Lemma Cint_S2I (x : algC) : x \is a Num.int -> x \is a s2Int.
Proof.
move=> Cx; apply/s2intP; exists (Num.floor x); exists 0.
by rewrite mul0r addr0 floorK.
Qed.

Lemma S2I_subring : subring_closed s2Int.
Proof.
split; try move=> x y /s2intP[a1 [a2->]] /s2intP[b1 [b2->]].
- by rewrite Cint_S2I.
- apply/s2intP; exists (a1 - b1); exists (a2 - b2).
  rewrite !raddfB /= mulrBl -!addrA; congr (_ + _).
  by rewrite addrCA -opprD.
apply/s2intP; exists (a1 * b1 + 2%:R * a2 * b2); exists (a1 * b2 + a2 * b1).
rewrite !(rmorph_nat,rmorphD, rmorphM) /= !(mulrDl, mulrDr, mul1r).
(* this should be ring *)
rewrite !mulrA -!addrA; congr (_ + _).
rewrite addrC -!addrA addrC -!addrA [RHS]addrA; congr(_ + _).
  by rewrite mulrAC -[_ * ?[n] * ?n]mulrA -expr2 sqrtCK mulrDr mulr1 mulrDl.
by rewrite [_ * _ * _%:~R]mulrAC.
Qed.

Lemma s2Int_conj x : (x^* \is a s2Int) = (x \is a s2Int).
Proof.
by (apply/idP/idP=> H; first rewrite -[x]conjCK); 
   rewrite conj_Creal // Creal_s2Int.
Qed.

HB.instance Definition _ := 
  GRing.isSubringClosed.Build algC s2Int_subdef S2I_subring.

Record S2I := S2Iof {
  algS2I :> algC;
  algS2IP : algS2I \is a s2Int }.

Hint Resolve algS2IP : core.

HB.instance Definition _ := [isSub for algS2I].
HB.instance Definition _ := [Countable of S2I by <:].
HB.instance Definition _ := [SubChoice_isSubComRing of S2I by <:].

Fact sQ2_proof : sqrtC 2%:R \is a s2Int.
Proof. by apply/s2intP; exists 0; exists 1; rewrite add0r mul1r. Qed.

Definition sQ2 := S2Iof sQ2_proof.

Definition invS2I (x : S2I) := insubd x (val x)^-1.
Definition unitS2I (x : S2I) :=
  (x != 0) && ((val x)^-1 \is a s2Int).

Fact mulS2Ir : {in unitS2I, left_inverse 1 invS2I *%R}.
Proof.
move=> x /andP [x_neq0 xVS2I]; rewrite /invS2I.
by apply: val_inj; rewrite /= insubdK // mulVr ?unitfE.
Qed.

Fact unitS2IP (x y : S2I) : y * x = 1 -> unitS2I x.
Proof.
rewrite /unitS2I => /(congr1 val) /=.
have [-> /eqP|x_neq0] := altP (x =P 0); first by rewrite mulr0 eq_sym oner_eq0.
by move=> /(canRL (mulfK x_neq0)); rewrite mul1r => <- /=.
Qed.

Fact unitS2I_out : {in [predC unitS2I], invS2I =1 id}.
Proof.
move=> x; rewrite inE /= -topredE /= /unitS2I.
rewrite negb_and negbK => /predU1P [->|/negPf xS2IF];
by apply: val_inj; rewrite /invS2I ?val_insubd /= ?xS2IF // invr0 if_same.
Qed.


HB.instance Definition _ := 
  GRing.ComRing_hasMulInverse.Build S2I mulS2Ir unitS2IP unitS2I_out.

Fact algS2I_sub : {morph algS2I : a b / a - b}.
Proof. by []. Qed.

Fact algS2I_multiplicative : multiplicative algS2I.
Proof. by []. Qed.

HB.instance Definition _ := GRing.isAdditive.Build S2I algC algS2I algS2I_sub.
HB.instance Definition _ :=
  GRing.isMultiplicative.Build S2I algC algS2I algS2I_multiplicative.

Lemma algS2I_mulrn x n : algS2I (x *+ n) = (algS2I x) *+ n.
Proof. by elim: n => //= n IH; rewrite !mulrS raddfD /= IH. Qed.

Definition conjs2i x : algC := (s2intA x)%:~R - (s2intB x)%:~R * sqrtC 2%:R.

Fact conjS2I_subproof (x : S2I) : conjs2i (val x) \is a s2Int.
Proof.
apply/s2intP; exists (s2intA (val x)); exists (-(s2intB (val x))).
by rewrite raddfN mulNr.
Qed.

Canonical conjS2I x := S2Iof (conjS2I_subproof x).

Lemma s2int_eqE a b c d : 
  (a%:~R + b%:~R * sqrtC 2%:R == c%:~R + d%:~R * sqrtC 2%:R :> algC) =
  ((a == c) && (b == d)).
Proof.
apply/idP/idP=> [|/andP[/eqP->/eqP->]//].
have [/eqP->|bDd HE] := boolP (b == d).
  by move/eqP/addIr/eqP; rewrite andbT eqr_int.
have /eqP[] := rat_irr2 ((a - c)%:~R /  (d - b)%:~R).
rewrite exprMn -!rmorphXn /= -[_%:~R]ratCK ratr_int rmorphXn raddfB /=.
rewrite -[a%:~R](addrK (b%:~R * sqrtC 2%:R)) (eqP HE).
rewrite -[_%:~R + _ + _]addrA -mulrBl [_%:~R + _ ]addrC addrK.
rewrite exprMn sqrtCK -raddfB -rmorphXn /= -mulrz_nat.
rewrite -rmorphM /= -[(_ * Posz _)%:~R]ratr_int ratCK.
rewrite rmorphM /= mulrAC rmorphXn /= -exprMn mulfV ?mul1r //.
by rewrite (eqr_int _ _ 0) subr_eq0 eq_sym.
Qed.

Lemma subS2I_rect (R : ringType) (a b c d z : R) : 
   (a + b * z) - (c + d * z) = (a - c) + (b - d) * z.
Proof.
by rewrite opprD addrA [a + _ - _]addrAC -!addrA -mulrBl !addrA.
Qed.

Fact s2intA_sub (a b : algC) :
  a \is a s2Int -> b \is a s2Int -> s2intA(a - b) = s2intA a - s2intA b.
Proof.
move=> Sa Sb.
have /eqP : a - b \is a s2Int by rewrite rpredB.
rewrite {1}(eqP Sa) {1}(eqP Sb) => /eqP.
by rewrite subS2I_rect -!raddfB s2int_eqE eq_sym => /andP[/eqP].
Qed.

Lemma s2intB_sub (a b : algC) :
  a \is a s2Int -> b \is a s2Int -> s2intB(a - b) = s2intB a - s2intB b.
Proof.
move=> Sa Sb.
have /eqP : a - b \is a s2Int by rewrite rpredB.
rewrite {1}(eqP Sa) {1}(eqP Sb) => /eqP.
by rewrite subS2I_rect -!raddfB s2int_eqE eq_sym => /andP[_ /eqP].
Qed.

Fact conjS2I_sub : {morph conjS2I : a b / a - b}.
Proof.
move=> a b; apply/val_eqP.
rewrite /= /conjs2i s2intA_sub // s2intB_sub //.
by rewrite -![-(_%:~R * _)]mulNr subS2I_rect -opprD !mulNr -!raddfB.
Qed.

HB.instance Definition _ := GRing.isAdditive.Build S2I S2I conjS2I conjS2I_sub.

Lemma mulS2I_rect a b c d : 
   (a + b * sqrtC 2%:R) * (c + d * sqrtC 2%:R) =
   (a * c + 2%:R * b * d) + (a * d + b * c) * sqrtC 2%:R :> algC.
Proof.
(* This should be ring *)
rewrite !(mulrDl, mulrDr, mul1r) !mulrA -!addrA; congr (_ + _).
rewrite addrC -!addrA addrC -!addrA [RHS]addrA; congr(_ + _).
  by rewrite mulrAC -[_ * ?[n] * ?n]mulrA -expr2 sqrtCK mulrDr mulr1 mulrDl.
by rewrite [_ * _ * c]mulrAC.
Qed.

Fact s2intA_mul (a b : algC) :
  a \is a s2Int -> b \is a s2Int -> 
  s2intA(a * b) = s2intA a * s2intA b + 2%:R * s2intB a * s2intB b.
Proof.
move=> Sa Sb.
have /eqP : a * b \is a s2Int by rewrite rpredM.
rewrite {1}(eqP Sa) {1}(eqP Sb)  mulS2I_rect => /eqP.
by rewrite  -mulrz_nat -!rmorphM /= -!rmorphD /= s2int_eqE => /andP[/eqP].
Qed.

Fact s2intB_mul (a b : algC) :
  a \is a s2Int -> b \is a s2Int -> 
  s2intB(a * b) = s2intA a * s2intB b + s2intB a * s2intA b.
Proof.
move=> Sa Sb.
have /eqP : a * b \is a s2Int by rewrite rpredM.
rewrite {1}(eqP Sa) {1}(eqP Sb) mulS2I_rect => /eqP.
by rewrite  -mulrz_nat -!rmorphM /= -!rmorphD /= s2int_eqE => /andP[_ /eqP].
Qed.

Fact s2intA_int (a : int) : s2intA (a%:~R) = a.
Proof.
have : a%:~R == a%:~R + 0%:~R * sqrtC 2%:R :> algC
  by rewrite mul0r addr0.
by rewrite {1}(eqP (Cint_S2I (intr_int _ a))) s2int_eqE => /andP[/eqP].
Qed.

Fact s2intA_nat (a : nat) : s2intA (a%:R) = a%:R.
Proof. by rewrite -mulrz_nat s2intA_int. Qed.

Fact s2intB_int (a : int) : s2intB (a%:~R) = 0.
Proof.
have : a%:~R == a%:~R + 0%:~R * sqrtC 2%:R :> algC.
  by rewrite mul0r addr0.
by rewrite {1}(eqP (Cint_S2I (intr_int _ a))) s2int_eqE => /andP[_ /eqP].
Qed.

Fact s2intB_nat (a : nat) : s2intB (a%:R) = 0.
Proof. by rewrite -mulrz_nat s2intB_int. Qed.

Fact s2intAN (a : algC) : a \is a s2Int -> s2intA(-a) = - s2intA a.
Proof.
move=> Sa.
have /eqP/eqP : -a  \is a s2Int by rewrite rpredN.
rewrite {1}(eqP Sa) -[-a]sub0r s2intA_sub ?rpred0 //.
rewrite  s2intB_sub ?rpred0 // (s2intA_nat 0) (s2intB_nat 0) !sub0r.
by rewrite opprD -mulNr -!raddfN /= s2int_eqE => /andP[/eqP].
Qed.

Fact s2intBN (a : algC) : a \is a s2Int -> s2intB(-a) = - s2intB a.
Proof.
move=> Sa.
have /eqP/eqP : -a  \is a s2Int by rewrite rpredN.
rewrite {1}(eqP Sa) -[-a]sub0r s2intA_sub ?rpred0 //.
rewrite  s2intB_sub ?rpred0 // (s2intA_nat 0) (s2intB_nat 0) !sub0r.
by rewrite opprD -mulNr -!raddfN /= s2int_eqE => /andP[_ /eqP].
Qed.

Lemma s2intA_add (a b : algC) :
  a \is a s2Int -> b \is a s2Int -> s2intA (a + b) = s2intA a + s2intA b.
Proof.
move=> Sa Sb.
by rewrite -{1}[b]opprK  s2intA_sub ?rpredN // s2intAN // opprK.
Qed.

Lemma s2intA_sum (I : eqType) (r : seq _) (P : pred I) E :
  (forall i, i \in r -> P i -> E i \is a s2Int) ->
  s2intA (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) s2intA (E i).
Proof.
elim: r => [H|a r IH H]; first by rewrite !big_nil (s2intA_nat 0).
rewrite !big_cons.
have H1 i : i \in r -> P i -> E i \is a s2Int.
  by move=> iIr Pi; apply: H; rewrite ?in_cons ?iIr ?orbT //.
case U : (P a); last by apply: IH.
rewrite s2intA_add ?IH ?H ?in_cons ?eqxx //.
elim: (r) H1 => [|b r1 IH1 H1]; first by rewrite big_nil // rpred0.
rewrite big_cons.
have H2 i : i \in r1 -> P i -> E i \is a s2Int.
  by move=> iIr Pi; apply: H1; rewrite ?in_cons ?iIr ?orbT.
case V : (P b); last by apply: IH1.
by rewrite rpredD ?IH1 // H1 // in_cons eqxx.
Qed.

Lemma s2intB_add (a b : algC) :
  a \is a s2Int -> b \is a s2Int -> s2intB (a + b) = s2intB a + s2intB b.
Proof.
move=> Sa Sb.
by rewrite -{1}[b]opprK  s2intB_sub ?rpredN // s2intBN // opprK.
Qed.

Lemma s2intB_sum (I : eqType) (r : seq _) (P : pred I) E :
  (forall i, i \in r -> P i -> E i \is a s2Int) ->
  s2intB (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) s2intB (E i).
Proof.
elim: r => [H|a r IH H]; first by rewrite !big_nil (s2intB_nat 0).
rewrite !big_cons.
have H1 i : i \in r -> P i -> E i \is a s2Int.
  by move=> iIr Pi; apply: H; rewrite ?in_cons ?iIr ?orbT //.
case U : (P a); last by apply: IH.
rewrite s2intB_add ?IH ?H ?in_cons ?eqxx //.
elim: (r) H1 => [|b r1 IH1 H1]; first by rewrite big_nil // rpred0.
rewrite big_cons.
have H2 i : i \in r1 -> P i -> E i \is a s2Int.
  by move=> iIr Pi; apply: H1; rewrite ?in_cons ?iIr ?orbT.
case V : (P b); last by apply: IH1.
by rewrite rpredD ?IH1 // H1 // in_cons eqxx.
Qed.

Fact conjS2I_multiplicative : multiplicative conjS2I.
Proof.
(split=> [a b|]; apply/val_eqP=> /=); last first.
   by rewrite /conjs2i (s2intA_nat 1) (s2intB_nat 1) mul0r subr0 mulrz_nat.
rewrite /= /conjs2i s2intA_mul // s2intB_mul //.
rewrite -![-(_%:~R * _)]mulNr mulS2I_rect !(mulNr,mulrN).
have -> : 2%:R = 2%:~R :> algC by [].
rewrite -!rmorphM -!raddfN -!raddfD /= .
rewrite -mulNr -raddfN -raddfB /=.
by rewrite /= s2int_eqE opprK !eqxx.
Qed.

Lemma s2intA_sqrt_eq1 x :
  x \is a s2Int -> s2intA (x ^+ 2) = 1 -> (x == -1) || (x == 1).
Proof.
move=> xS /eqP.
have /eqP{2 3}-> := xS.
have x2S : x ^+2 \is a s2Int by rewrite rpredX.
rewrite expr2 s2intA_mul // -mulrA -!expr2.
have [/eqP ZB|nZB] := boolP (s2intB x == 0).
  rewrite ZB expr0n !mulr0 !mul0r !addr0 sqrf_eq1.
  rewrite -(@eqr_int (Num.NumDomain.clone _ algC)) orbC.
  by rewrite  -(@eqr_int (Num.NumDomain.clone _ algC)) raddfN.
move=> H.
suff : 0 + 2%:R * 1 <= s2intA x ^+ 2 + 2%:R * s2intB x ^+ 2.
  by rewrite (eqP H) add0r mulr1 (ler_nat _ _ 1).
rewrite lerD ?sqr_ge0 // ler_pM // -gtz0_ge1.
rewrite real_exprn_even_gt0 //.
by rewrite qualifE //=; case: lerP => H1; rewrite //= ltW.
Qed.

Lemma s2intA_sqrt_gt1 x : x \is a s2Int -> x != 0 -> 1 <= s2intA (x ^+ 2).
Proof.
move=> xS nZx.
have x2S : x ^+2 \is a s2Int by rewrite rpredX.
rewrite expr2 s2intA_mul // -mulrA -!expr2.
have [/eqP ZA|nZA] := boolP (s2intA x == 0).
  rewrite ZA expr0n add0r.
  have [/eqP ZB|nZB] := boolP (s2intB x == 0).
    by case/negP: nZx; rewrite (eqP xS) ZA ZB mul0r add0r.
  apply: le_trans (_ : 1 <= 1 * s2intB x ^+ 2) _.
    rewrite mul1r -[_ ^+2]gez0_abs ?sqr_ge0 //.
    by rewrite abszX lez_nat expn_gt0 absz_gt0 nZB.
  by rewrite ler_pM // sqr_ge0.
apply: le_trans (_ : 1 <= s2intA x ^+ 2 + 0) _.
  rewrite addr0 -[_ ^+2]gez0_abs ?sqr_ge0 //.
  by rewrite abszX lez_nat expn_gt0 absz_gt0 nZA.
by rewrite lerD // mulr_ge0 // sqr_ge0.
Qed.

HB.instance Definition _ :=
  GRing.isMultiplicative.Build S2I S2I conjS2I conjS2I_multiplicative.

Lemma algS2I_nat n : algS2I n%:R = n%:R.
Proof. by elim: n => //= n IH; rewrite -addn1 !natrD -IH. Qed.

Lemma algS2I_int z : algS2I z%:~R = z%:~R.
Proof. by case: z => n; rewrite ?raddfN /= algS2I_nat. Qed.

Lemma conjS2I_nat n : conjS2I n%:R = n%:R.
Proof.
apply/val_eqP.
by rewrite /= /conjs2i algS2I_nat s2intA_nat s2intB_nat mul0r subr0 mulrz_nat.
Qed.

Lemma conjS2I_int z : conjS2I z%:~R = z%:~R.
Proof. by case: z => n; rewrite ?rmorphN /= conjS2I_nat. Qed.

Lemma sqrt2_S2I : sqrtC 2%:R \is a s2Int.
Proof. by apply/s2intP; exists 0; exists 1; rewrite add0r mul1r. Qed.

Fact s2intA_sqrt (a : algC) :
  a \is a s2Int -> s2intA(a * sqrtC 2%:R) = 2%:R * s2intB a.
Proof.
move=> Sa.
have : a * sqrtC 2%:R \is a s2Int by rewrite rpredM // sqrt2_S2I.
rewrite s2IntE {1}(eqP Sa) addrC mulrDl -mulrA -expr2 sqrtCK mulrC.
by rewrite -mulrz_nat -rmorphM /= s2int_eqE => /andP[/eqP].
Qed.

Fact s2intB_sqrt (a : algC) :
  a \is a s2Int -> s2intB(a * sqrtC 2%:R) = s2intA a.
Proof.
move=> Sa.
have : a * sqrtC 2%:R \is a s2Int by rewrite rpredM // sqrt2_S2I.
rewrite s2IntE {1}(eqP Sa) addrC mulrDl -mulrA -expr2 sqrtCK mulrC.
by rewrite -mulrz_nat -rmorphM /= s2int_eqE => /andP[_ /eqP].
Qed.

Lemma s2intA_rect z1 z2 : s2intA (z1%:~R + z2%:~R * sqrtC 2%:R) = z1.
Proof.
rewrite s2intA_add ?rpredM ?sqrt2_S2I ?Cint_S2I ?intr_int //.
by rewrite s2intA_int s2intA_sqrt ?Cint_S2I ?intr_int // s2intB_int mulr0 addr0.
Qed.

Lemma s2intB_rect z1 z2 : s2intB (z1%:~R + z2%:~R * sqrtC 2%:R) = z2.
Proof.
rewrite s2intB_add ?rpredM ?sqrt2_S2I ?Cint_S2I ?intr_int //.
by rewrite s2intB_int s2intB_sqrt ?Cint_S2I ?intr_int // s2intA_int add0r.
Qed.

Lemma conjS2I_sQ2 : conjS2I sQ2 = - sQ2.
Proof.
apply/val_eqP => /=.
rewrite /conjs2i -[sqrtC _]mul1r !(s2intA_sqrt, s2intB_sqrt)  ?rpred1 //.
by rewrite (s2intA_nat 1) (s2intB_nat 1) mulr0 sub0r !mul1r.
Qed.

Lemma conjS2IK : involutive conjS2I.
Proof.
move=> x; apply/val_eqP => /=.
rewrite /conjs2i !(s2intA_sub, s2intB_sub) 
        ?rpredM ?(Cint_S2I (intr_int _ _), sqrt2_S2I) //.
rewrite !(s2intA_sqrt,s2intB_sqrt) ?(Cint_S2I (intr_int _ _), sqrt2_S2I) //.
rewrite !s2intA_int !s2intB_int mulr0 subr0 sub0r raddfN mulNr opprK /=.
by rewrite eq_sym // [_ == _]algS2IP.
Qed.

Notation " a ^@ " := (conjs2i a) (at level 10).

Definition s2intNorm (x : algC) := x * x^@.

Lemma s2intNormCint (x : S2I) : s2intNorm (val x) \in Num.int.
Proof.
rewrite /s2intNorm.
have /eqP/= {1}-> := algS2IP x.
rewrite /conjs2i -mulNr  mulS2I_rect !mulrN rpredD //; last first.
  by rewrite [_%:~R * _]mulrC addrC subrr mul0r int_num0.
by rewrite rpredB // !rpredM ?intr_int  // intr_nat.
Qed.

Declare Scope S2I_scope.
Delimit Scope S2I_scope with S2I.

Open Scope S2I_scope.

Definition normS2I (x : S2I) : nat := `|Num.floor (s2intNorm (val x))|.
Local Notation "'N x" := (normS2I x%R) (at level 10) : S2I_scope.

Lemma normS2IE (x : S2I) : 'N x = `|Num.floor (val (x * conjS2I x)%R)|%N.
Proof. by []. Qed.

Lemma s2intNorm0 : s2intNorm 0 = 0.
Proof. by rewrite /s2intNorm mul0r. Qed.

Lemma normS2I0 : 'N 0 = 0%N.
Proof. by rewrite /normS2I s2intNorm0 (intrKfloor 0). Qed.

Lemma s2intNorm1 : s2intNorm 1 = 1.
Proof. 
have /val_eqP/=/eqP : conjS2I 1 = 1 by rewrite rmorph1.
by rewrite /s2intNorm mul1r => ->.
Qed.

Lemma normS2I1 : 'N 1 = 1%N.
Proof. by rewrite /normS2I s2intNorm1 (intrKfloor 1). Qed.

Lemma normS2IN x : 'N (- x) = 'N x.
Proof.  by rewrite normS2IE rmorphN /= mulNr mulrN opprK. Qed.

Lemma s2intNormM x y : x \is a s2Int -> y \is a s2Int ->
  s2intNorm (x * y) = s2intNorm x * s2intNorm y.
Proof.
move=> xS yS; rewrite /s2intNorm.
have /val_eqP/eqP/=-> := 
  rmorphM (GRing.RMorphism.clone _ _ _ conjS2I) (S2Iof xS) (S2Iof yS).
by rewrite -!mulrA; congr (_ * _); rewrite mulrCA.
Qed.

Lemma normS2IM x y : 'N (x * y) = ('N x * 'N y)%N.
Proof. 
rewrite normS2IE [conjS2I _]rmorphM /= -!mulrA [algS2I y * (_ * _)]mulrCA.
by rewrite !mulrA -mulrA floorM ?abszM // s2intNormCint.
Qed.

Lemma normS2IX x n : 'N (x ^+ n) = ('N x ^ n)%N.
Proof.
elim: n => [|n IH]; first by rewrite expr0 normS2I1 expn0.
by rewrite exprS normS2IM IH expnS.
Qed.

Lemma normS2I_conj x : 'N (conjS2I x) = 'N x.
Proof. by rewrite !normS2IE conjS2IK mulrC. Qed.

Lemma normS2IEAB (x : S2I) : 
  'N x = `|(s2intA x ^+ 2 - 2%:R * (s2intB x ^+ 2))%R|%N.
Proof.
rewrite /normS2I /s2intNorm.
have /eqP/= {1}-> := algS2IP x.
rewrite /conjs2i -mulNr  mulS2I_rect !mulrN.
rewrite [X in -X + _]mulrC addNr mul0r addr0 -mulrA.
by rewrite -mulrz_nat -!rmorphM -rmorphB /= intrKfloor.
Qed.

Lemma normS2I_eq0 (x : S2I) : ('N x == 0%N) = (x == 0).
Proof.
have /charf0P<- := Cchar.
rewrite normS2IEAB (eqr_nat _ _ 0) absz_eq0 subr_eq0 int_irr2E.
apply/idP/eqP => [/andP[/eqP H1 /eqP H2]|->]; last first.
  by rewrite (s2intA_nat 0) (s2intB_nat 0).
by apply/val_eqP; rewrite /= (eqP (algS2IP x)) H1 H2 mul0r add0r.
Qed.

Lemma normS2I_gt0 (x : S2I) : ('N x > 0)%N = (x != 0).
Proof. by rewrite ltn_neqAle andbT eq_sym normS2I_eq0. Qed.

Lemma normS2I_le (x y : S2I) : y != 0 -> ('N x <= 'N (x * y))%N.
Proof.
rewrite -!normS2I_eq0 normS2IM; case: ('N _) => // n _.
by rewrite leq_pmulr.
Qed.

Lemma normS2I_nat n : 'N n%:R = (n ^ 2)%N.
Proof.
rewrite normS2IE /= /conjs2i algS2I_nat s2intA_nat s2intB_nat.
by rewrite mul0r subr0 -mulrz_nat -intrM intrKfloor -natrM natz.
Qed.

Lemma normS2I_int z : 'N z%:~R = (`|z| ^ 2)%N.
Proof. by case: z => /= n; rewrite ?normS2IN normS2I_nat. Qed.

Lemma algS2I_eqE  (x y : S2I) : 
   (x == y) = ((s2intA x == s2intA y) && (s2intB x == s2intB y)).
Proof.
apply/eqP/andP=> [->//|[/eqP H1 /eqP H2]].
apply/val_eqP => /=.
have /eqP-> := algS2IP x.
by rewrite (eqP (algS2IP y)) H1 H2 -(eqP (algS2IP y)).
Qed.

Lemma normS2I_unit (x : S2I) : ('N(x) == 1)%N = (x \in GRing.unit).
Proof.
apply/eqP/idP=> [|/GRing.unitrPr[y xyE]]; last first.
  have /eqP := normS2I_nat 1.
  by rewrite exp1n -xyE mulr1n normS2IM muln_eq1 => /andP[/eqP].
rewrite /normS2I /s2intNorm; set u := Num.floor _ => H.
apply/GRing.unitrPr.
case: (lerP 0 u) => Hu.
  have := gez0_abs Hu; rewrite H /= => Hv.
  exists (conjS2I x); apply/val_eqP => /=.
  have := floorK (s2intNormCint x).
  by rewrite /s2intNorm -/u -Hv => <-.
have := ltz0_abs Hu; rewrite H /= => Hv.
exists (-(conjS2I x)); apply/val_eqP => /=.
have := floorK (s2intNormCint x).
rewrite mulrN /s2intNorm -/u => <-.
by rewrite -raddfN /= -Hv.
Qed.

Fact S2I_idomainAxiom (x y : S2I) : x * y = 0 -> (x == 0) || (y == 0).
Proof.
move=> /(congr1 normS2I) /= /eqP.
by rewrite normS2IM normS2I0 muln_eq0 !normS2I_eq0.
Qed.

HB.instance Definition _ := GRing.ComUnitRing_isIntegral.Build S2I
                                    S2I_idomainAxiom.

Lemma sQ2K : sQ2 ^+ 2 = 2%:R.
Proof. by apply/val_eqP; rewrite [val _]sqrtCK. Qed.

Fact norm1DsQ2 : 'N (1 + sQ2) = 1%N.
Proof.
rewrite normS2IE.
have -> : conjS2I (1 + sQ2) = 1 - sQ2.
  by rewrite rmorphD rmorph1 [X in (1 + X)]conjS2I_sQ2.
rewrite mulrC -subr_sqr expr1n sQ2K -opprB -(natrB _ (isT: 1 <= 2)%N) mulr1n.
by rewrite (intrKfloor (-1)) abszN1.
Qed.

Lemma normS2I_eq1P (x : S2I) : 
  reflect 
   (exists b : bool, exists i : int, 
       x = (-1) ^+ b * (1 + sQ2) ^ i)
   ('N x == 1)%N.
Proof.
have F1 : 1 + sQ2 \is a GRing.unit.
  by rewrite -normS2I_unit norm1DsQ2.
apply: (iffP idP) => [|[b [i->]]]; last first.
  rewrite normS2IM normS2IX normS2IN normS2I1.
  rewrite exp1n mul1n normS2IE rmorphXz //=.
  rewrite -rmorphM -exprzMl //=; last first.
    by rewrite -normS2I_unit normS2I_conj norm1DsQ2.
  rewrite rmorphD /= rmorph1 conjS2I_sQ2.
  rewrite mulrC -subr_sqr expr1n sQ2K -opprB -(natrB _ (isT: 1 <= 2)%N) mulr1n.
  rewrite rmorphXz ?rpredN ?rpred1 //= expN1r.
  by rewrite floorX ?rpredN //= // floorN // floor1 // absz_sign.
wlog : x / (0 <= s2intB x) => [H HN|].
  have [PB|NB] := lerP 0 (s2intB x); first by apply: H.
  case (H (-x)) => [||b [i Hbi]].
  - by rewrite raddfN s2intBN //= oppr_ge0 ltW.
  - by rewrite normS2IN.
  by exists (~~ b); exists i; rewrite signrN mulNr -Hbi opprK.
elim: {x}_.+1 {-2}x (ltnSn (`|s2intB (algS2I x)|)) => // [] [|n] IH x.
  rewrite ltnS leqn0 absz_eq0 => /eqP B0 _ Nx.
  exists (s2intA x < 0); exists 0; rewrite expr0z mulr1.
  apply/val_eqP => /=.
  move: Nx.
  rewrite normS2IEAB B0 mulr0 subr0 abszX (eqn_exp2r _ 1) // => /eqP Nx.
  have /eqP/= {1}-> := algS2IP x.
  rewrite B0 mul0r addr0 {1}[s2intA _]intEsign Nx mulr1 /=.
  by case: (_ < 0).
rewrite normS2IEAB le_eqVlt => Hs /orP[/eqP ZA |HP Nx].
  rewrite -ZA mulr0 subr0 abszX -{2}(exp1n 2) eqn_exp2r // => Nx.
  exists (s2intA (algS2I x) < 0); exists 0; apply/val_eqP.
  have /=/eqP{1}-> := algS2IP x.
  rewrite -ZA mulr1 mul0r addr0 /= -{1}[s2intA _]mulz_sign_abs (eqP Nx) mulr1.
  by case: (_ < 0).
pose a := `|s2intA x|; pose b := s2intB x.
have /andP[F2 F3] : b <= a < 2%:R * b.
  have F0a : a ^ 2 = s2intA x ^+ 2.
    by rewrite -[a ^ 2]normrX ger0_norm //sqr_ge0.
  have F1a : `|a ^ 2 - 2%:R * b ^ 2| = 1.
    by rewrite -abszE -[X in _ = Posz X](eqP Nx) F0a.
  have : `|a ^ 2 - 2%:R * b ^ 2| <= b ^ 2 by rewrite F1a exprn_ege1.
  rewrite ler_norml (_ : - b ^ 2 = b ^ 2 - 2%:R * b ^ 2); last first.
    by rewrite mulrDl mul1r opprD addrA subrr add0r.
  rewrite lerD2r -subr_ge0 subr_sqr pmulr_lge0; last first.
    by rewrite (lt_le_trans HP) // -[X in X <= _]add0r lerD.
  rewrite subr_ge0 => /andP[->/= HH].
  have : a ^ 2  < (2%:R * b) ^ 2.
    rewrite -[a ^ 2](subrK (2%:R * b ^ 2)).
    rewrite [X in _ < X]exprMn -natrX (_ : 2 ^ 2 = 2 + 2)%N //.
    rewrite  natrD [X in _ < X]mulrDl.
    rewrite ltrD2r (le_lt_trans HH) // mulrDl mul1r -[X in X < _]add0r.
    by rewrite ltrD2r // exprn_even_gt0 // lt0r_neq0.
  rewrite -subr_gt0 subr_sqr pmulr_lgt0 1?subr_gt0 //.
  rewrite (lt_le_trans HP) // mulrDl mul1r -addrA -[X in X <= _]addr0.
  by rewrite lerD2l -[X in X <= _]addr0 lerD // ltW.
case: (ltrgtP (s2intA x) 0) => HH; last first.
  - by rewrite HH add0r abszN abszM muln_eq1 in Nx.
  - pose y := x *  (sQ2 - 1).
    have aE : a = s2intA x by rewrite [a]ger0_norm // ltW.
    have yB : s2intB y = a - b.
      rewrite s2intB_mul //  s2intB_sub // (s2intB_nat 1) subr0.
    rewrite -[sQ2]mul1r s2intB_sqrt // (s2intA_nat 1) mulr1.
    rewrite s2intA_sub // (s2intA_nat 1) s2intA_sqrt // (s2intB_nat 1).
    by rewrite mulr0 sub0r mulrN mulr1 aE.
  have yA : s2intA y = 2%:R * b - a.
    rewrite s2intA_mul // s2intA_sub // (s2intA_nat 1).
    rewrite -[sQ2]mul1r s2intA_sqrt // (s2intB_nat 1) sub0r mulrN mulr1 -aE.
    rewrite s2intB_sub // (s2intB_nat 1) s2intB_sqrt // (s2intA_nat 1).
    by rewrite subr0 mulr1 addrC.
  case: (IH y) => [|||c [i Hci]].
  - rewrite ltnS in Hs; rewrite yB (leq_trans _ Hs) //.
    rewrite -ltz_nat -/b !gez0_abs ?subr_ge0 //.
    - by rewrite ltrBlDl -[b]mul1r -mulrDl.
    - by rewrite ltW.
   by rewrite yB subr_ge0.
  - rewrite normS2IM normS2IEAB (eqP Nx).
    rewrite -opprB normS2IN -normS2I_conj rmorphB /= rmorph1 conjS2I_sQ2 opprK.
    by rewrite norm1DsQ2.
  exists c; exists (i + 1).
  rewrite  exprzDr // expr1z mulrA -Hci -mulrA [1 + _]addrC.
  by rewrite -subr_sqr expr1n sQ2K -(natrB _ (isT: 1 <= 2)%N) mulr1.
pose y := -x * (1 + sQ2).
have aE : a = - s2intA x by rewrite [a]ler0_norm // ltW.
have yB : s2intB y = a - b.
  rewrite s2intB_mul // s2intB_add // (s2intB_nat 1) add0r.
  rewrite -[sQ2]mul1r s2intB_sqrt // (s2intA_nat 1) mulr1.
  rewrite s2intA_add // (s2intA_nat 1) s2intA_sqrt // (s2intB_nat 1).
  by rewrite mulr0 addr0 mulr1 s2intAN // -aE s2intBN .
have yA : s2intA y = a - 2%:R * b.
  rewrite s2intA_mul // s2intA_add // (s2intA_nat 1).
  rewrite -[sQ2]mul1r s2intA_sqrt // (s2intB_nat 1) mulr0 subr0 mulr1.
  rewrite s2intB_add // (s2intB_nat 1) s2intB_sqrt // (s2intA_nat 1).
  by rewrite add0r mulr1 s2intAN // -aE s2intBN // mulrN.
case: (IH y) => [|||c [i Hci]].
- rewrite ltnS in Hs; rewrite yB (leq_trans _ Hs) //.
  rewrite -ltz_nat -/b !gez0_abs ?subr_ge0 //.
  - by rewrite ltrBlDl -[b]mul1r -mulrDl.
  - by rewrite ltW.
  by rewrite yB subr_ge0.
- by rewrite normS2IM normS2IN normS2IEAB (eqP Nx) norm1DsQ2.
exists (~~ c); exists (i - 1).
apply: (mulIr F1).
rewrite -[LHS]opprK -mulNr [_ * _]Hci -{3}[1 + _]expr1z -mulrA -exprzDr // subrK.
by rewrite -mulNr; case: (c); rewrite // opprK. 
Qed.

Fact divS2I_subproof (x y : int) : x%:~R +  y%:~R * sqrtC 2%:R \is a s2Int.
Proof. by apply/s2intP; exists x; exists y. Qed.

Definition divS2I (x y : S2I) : S2I :=
  let za := s2intA x * s2intA y  - 2%:R * s2intB x * s2intB y in
  let zb := s2intB x * s2intA y - s2intA x * s2intB y in
  let n := Num.floor (s2intNorm y) in
  S2Iof (divS2I_subproof (cdivz za n) (cdivz zb n)).

Notation " x %/ y " := (divS2I x y) : S2I_scope.

Lemma divS2I0 x : x %/ 0 = 0.
Proof.
apply/val_eqP=> /=.
by rewrite !(s2intA_nat 0, s2intB_nat 0, mul0r, mulr0, subrr, cdiv0z, add0r).
Qed.

Lemma div0S2I y : 0 %/ y = 0.
Proof.
apply/val_eqP=> /=.
by rewrite !(s2intA_nat 0, s2intB_nat 0, mul0r, mulr0, subrr, cdiv0z, add0r).
Qed.

Lemma divS2I1 x : x %/ 1 = x.
Proof.
apply/val_eqP=> /=.
rewrite !(s2intA_nat 1, s2intB_nat 1, mulr1, mulr0, subr0).
by rewrite s2intNorm1 floor1 !cdivz1 eq_sym; exact: (algS2IP x).
Qed.

Lemma s2intNormE (x : S2I) :
  s2intNorm x = (s2intA x ^+ 2 -  2%:R * s2intB x ^+ 2)%:~R.
Proof.
rewrite /s2intNorm mulrC.
have /eqP{2}-> := algS2IP x.
rewrite -subr_sqr exprMn sqrtCK mulrC rmorphB /=. 
rewrite [in RHS]rmorphXn; congr (_ - _).
by rewrite [in RHS]rmorphM /= rmorphXn.
Qed.

Lemma divS2Ixx (x : S2I) : x != 0 -> x %/ x = 1.
Proof.
move=> xNz; apply/val_eqP => /=.
rewrite [s2intB _ * s2intA _]mulrC subrr cdiv0z mul0r addr0.
rewrite s2intNormE !intrKfloor.
set a := _ - _; set b := _ - _.
have abE : a = b  by rewrite /a /b !(expr1, exprS) !mulrA.
rewrite abE cdivzz // -abE.
by rewrite -absz_eq0 abE -normS2IEAB normS2I_eq0.
Qed.

Definition modS2I (x y : S2I) : S2I := x - (x %/ y)%S2I * y.

Notation " x %% y " := (modS2I x y) : S2I_scope.

Lemma modS2I0 x : x %% 0 = x.
Proof. 
by apply/val_eqP; rewrite /= !(s2intA_nat 0, s2intB_nat 0, mulr0, subr0).
Qed.

Lemma mod0S2I y : 0 %% y = 0.
Proof.
apply/val_eqP => /=. 
by rewrite !(s2intA_nat 0, s2intB_nat 0, mul0r, mulr0, addr0, subrr, cdiv0z).
Qed.

Lemma modS2I1 x : x %% 1 = 0.
Proof. by rewrite /modS2I divS2I1 mulr1 subrr. Qed.

Lemma divS2I_eq (x y : S2I) : x = (x %/ y)%S2I * y + (x %% y)%S2I.
Proof. by rewrite /modS2I addrC subrK. Qed.

Lemma ltn_modS2I (x y : S2I) : ('N (x %% y)%S2I < 'N y)%N = (y != 0).
Proof.
have [/eqP->|yNz] := boolP (y == 0).
  by rewrite normS2I0 modS2I0.
have /ltn_pmul2r<-: (0 < 'N(y) ^ 2)%N by rewrite sqrn_gt0 lt0n normS2I_eq0.
rewrite -{1}normS2I_int -!normS2IM /modS2I /divS2I.
rewrite s2intNormE intrKfloor.
set xa := s2intA _; set ya := s2intA _.
set xb := s2intB _; set yb := s2intB _.
set za : int := _ - _; set Ny : int := _ - _; set zb : int := _ * _ - _.
pose  t : algC := algS2I x / algS2I y * Ny%:~R.
have tE :  t = za%:~R + zb%:~R * sqrtC (2%:R).
  rewrite /t -s2intNormE /s2intNorm mulrA divfK // /conjs2i.
  have /eqP-> := algS2IP x.
  rewrite -mulNr mulS2I_rect !mulrN [- _ + _]addrC.
  by rewrite -!rmorphM /= -(intrM _ 2%:R) -rmorphM -!rmorphB.
have tS : t \is a s2Int by rewrite tE divS2I_subproof.
have tA : s2intA t = za.
  have /eqP/eqP := tS.
  by rewrite tE s2int_eqE => /andP[/eqP].
have tB : s2intB t = zb.
  have /eqP/eqP := tS.
  by rewrite tE s2int_eqE => /andP[_ /eqP].
rewrite ['N (_ * _)]/normS2I /= -[algS2I x](divfK yNz).
rewrite -mulrBl -mulrA -[algS2I y * _]mulrC mulrA algS2I_int mulrBl -/t.
rewrite tE [_ * _%:~R]mulrDl mulrAC.
rewrite {1}(cdivz_eq za Ny) {1}(cdivz_eq zb Ny).
rewrite subS2I_rect ![_ + cmodz _ _]addrC.
rewrite rmorphD /= rmorphM /= addrK.
rewrite [(_ + _)%:~R]rmorphD /= rmorphM /= addrK.
set xx := _ + _.
have sxx : xx \is a s2Int by apply/s2intP; eexists; eexists.
rewrite s2intNormM ?s2int //.
have /= -> := s2intNormE (S2Iof sxx).
rewrite floorM ?intr_int ?s2intNormCint // abszM.
rewrite mulnC ltn_pmul2l; last by rewrite lt0n normS2I_eq0.
rewrite s2intA_rect s2intB_rect intrKfloor.
set x1 : int := _ ^+ 2; set x2 : int := _ ^+ 2.
apply: leq_ltn_trans (_ : (`|x1| + 2 * `|x2| < _)%N).
  have := leqD_dist (x1) (x1 + 2%:R * x2) (2%:R * x2).
  rewrite opprD addrA subrr sub0r abszN abszM /= [X in (_ <= X)%N -> _]addnC.
  by rewrite addrK.
rewrite -(ltn_pmul2l (isT: (0 < 2 ^ 2)%N)) mulnDr.
apply: leq_ltn_trans (_ : (1 + 2) * 'N y ^ 2 < _)%N; last first.
  by rewrite ltn_mul2r sqrn_gt0 lt0n normS2I_eq0 yNz.
have NyE : `|Ny|%N = 'N y by rewrite normS2IEAB.
have NyP : Ny != 0 by rewrite -absz_eq0 NyE normS2I_eq0.
rewrite -NyE mulnDl mul1n leq_add //.
  by rewrite !abszX -!expnMn leq_exp2r //
       -(@ler_nat (Num.NumDomain.clone _ int)) natrM !natz cmodz_lt.
rewrite mulnCA leq_mul2l /=.
by rewrite !abszX -!expnMn leq_exp2r //
     -(@ler_nat (Num.NumDomain.clone _ int)) natrM !natz cmodz_lt.
Qed.

Lemma ltn_modS2IN0 x y : y != 0 -> ('N (x %% y)%S2I < 'N y)%N.
Proof. by rewrite ltn_modS2I. Qed.

Lemma modS2Ixx x : (x %% x)%S2I = 0.
Proof.
have [/eqP->|xNz] := boolP (x == 0); first by rewrite mod0S2I.
by rewrite /modS2I divS2Ixx // mul1r subrr.
Qed.

Lemma divS2IKl (x y : S2I) : x != 0 -> (y * x %/ x) = y.
Proof.
move=> xNz.
apply/eqP; rewrite eq_sym -subr_eq0.
have := xNz; rewrite -(ltn_modS2I (y * x)).
have -> : ((y * x) %% x)%S2I  = (y - ((y * x) %/ x)%S2I) * x.
  by rewrite mulrBl {2}(divS2I_eq (y * x) x) [_ + (_ %% _)%S2I]addrC addrK.
by rewrite normS2IM -{2}['N x]mul1n ltn_mul2r ltnS leqn0 normS2I_eq0 => /andP[].
Qed.

Lemma divS2IKr (x y : S2I) : x != 0 -> (x * y %/ x) = y.
Proof. by rewrite mulrC; exact: divS2IKl. Qed.

Lemma modS2IKl (x y : S2I) : (y * x %% x) = 0.
Proof.
have [/eqP->|xNz] := boolP (x == 0); first by rewrite modS2I0 mulr0.
by rewrite /modS2I divS2IKl // subrr.
Qed.

Lemma modS2IKr (x y : S2I) : (x * y %% x) = 0.
Proof. by rewrite mulrC modS2IKl. Qed.

Definition dvdS2I x y := (y %% x)%S2I == 0.

Notation " x %| y " := (dvdS2I x y) : S2I_scope.

Lemma dvdS2I0 x : (x %| 0)%S2I.
Proof. by rewrite /dvdS2I mod0S2I. Qed.

Lemma dvdS2IP (x y : S2I) :
  reflect (exists q : S2I, y = q * x) (x %| y)%S2I.
Proof.
apply: (iffP idP) => [/eqP xDy|[q ->]].
  exists (y %/ x)%S2I; first by rewrite {1}(divS2I_eq y x) xDy addr0.
by rewrite /dvdS2I modS2IKl.
Qed.

Lemma dvd0S2I x : (0 %| x) = (x == 0).
Proof.
apply/dvdS2IP/eqP => [[q ->]|->]; first by rewrite mulr0.
by exists 0; rewrite mulr0.
Qed.

Lemma dvdS2I_mull z x y : (x %| y) -> (x %| z * y).
Proof. by move=> /dvdS2IP[u ->]; apply/dvdS2IP; exists (z * u); exact: mulrA. Qed.

Lemma dvdS2I_mulr z x y : (x %| y) -> (x %| y * z).
Proof. by rewrite mulrC; exact: dvdS2I_mull. Qed.

Lemma dvdS2Ixx x : x %| x.
Proof. by rewrite /dvdS2I modS2Ixx. Qed.

Lemma dvdS2I_norm x y : x %| y -> ('N x %| 'N y)%N.
Proof. by move=> /dvdS2IP[z ->]; rewrite normS2IM dvdn_mull // dvdnn. Qed.

Lemma dvd1S2I x : (1 %| x) .
Proof. by apply/dvdS2IP; exists x; rewrite mulr1. Qed.

Lemma dvdS2I1 x : (x %| 1) = ('N x == 1%N).
Proof.
apply/idP/idP => [H|].
  by have := dvdS2I_norm H; rewrite normS2I1 dvdn1.
rewrite normS2I_unit => H; apply/dvdS2IP; exists x^-1.
by apply/eqP; rewrite mulrC eq_sym -unitrE.
Qed.

Lemma divS2IK (x y : S2I) : x %| y -> (y %/ x)%S2I * x = y.
Proof.
have [/eqP->|nZx /dvdS2IP[q ->]] := boolP (x == 0).
  by rewrite dvd0S2I mulr0 => /eqP->.
by rewrite divS2IKl.
Qed.

Lemma dvdS2I_add x y z:  (x %| y) -> (x %| z) -> (x %| y + z).
Proof.
move=> /dvdS2IP[q1->] /dvdS2IP[q2->]; apply/dvdS2IP; exists (q1 + q2).
by rewrite mulrDl.
Qed.

Lemma dvdS2I_nat_dvdz_A n x : n%:R %| x -> (n %| `|s2intA x|)%N.
Proof.
case/dvdS2IP=> q /val_eqP/eqP/(congr1 s2intA) /= ->.
rewrite s2intA_mul // algS2I_nat s2intA_nat s2intB_nat !mulr0 addr0.
apply/dvdnP; exists `|s2intA q|%N.
by rewrite abszM  natz.
Qed.

Lemma dvdS2I_nat_dvdz_B n x : n%:R %| x -> (n %| `|s2intB x|)%N.
Proof.
case/dvdS2IP=> q /val_eqP/eqP/(congr1 s2intB) /= ->.
rewrite s2intB_mul // algS2I_nat s2intA_nat s2intB_nat !mulr0 add0r.
apply/dvdnP; exists `|s2intB q|%N.
by rewrite abszM  natz.
Qed.

Lemma conjS2I_dvd x y : x %| y -> (conjS2I x) %| (conjS2I y).
Proof.
case/dvdS2IP=> q ->; apply/dvdS2IP; exists (conjS2I q).
by rewrite rmorphM.
Qed.


Fixpoint gcdS2I_rec (n : nat) (xx  yy : S2I) {struct n} :=
   let rr := modS2I xx yy in
   if rr == 0 then yy else
   if n is n1.+1 then gcdS2I_rec n1 yy rr else rr.

Definition gcdS2I x y :=
  let: (x1, y1) := if ('N x < 'N y)%N then (y, x) else (x, y) in
  if x1 == 0 then y1 else
  gcdS2I_rec ('N x1) x1 y1.

Lemma gcd0S2I : left_id 0 gcdS2I.
Proof.
move=> x; rewrite /gcdS2I.
have [/eqP->|xNz]:= boolP (x == 0).
  by rewrite ltnn eqxx.
rewrite normS2I0 normS2I_gt0 xNz (negPf xNz).
have : 'N x != 0%N by rewrite normS2I_eq0.
by case: ('N _) => [|[|v]]; rewrite //= !(mod0S2I, modS2I0) (negPf xNz) eqxx.
Qed.

Lemma gcdS2I0 : right_id 0 gcdS2I.
Proof.
move=> x; rewrite /gcdS2I.
have [/eqP->|xNz]:= boolP (x == 0).
  by rewrite ltnn eqxx.
rewrite normS2I0 /= (negPf xNz).
by case: ('N _) => [|[|v]] //=  ; rewrite !(modS2I0,mod0S2I) (negPf xNz) ?eqxx.
Qed.

Lemma gcdS2I_recE m n x y : ('N y <= m)%N -> ('N y <= n)%N
      -> ('N y < 'N x)%N -> gcdS2I_rec m x y = gcdS2I_rec n x y.
Proof.
elim: m n x y => [|m Hrec] [|n] //= x1 y1.
 - rewrite leqn0 normS2I_eq0 => /eqP=> -> _.
   rewrite normS2I0 normS2I_gt0 modS2I0 => /negPf-> /=.
   by case: n => [|n]; rewrite /= mod0S2I eqxx.
 - rewrite leqn0 normS2I_eq0 => _ /eqP=> -> _.
   rewrite modS2I0; case: (boolP (x1 == 0)) => // x1Nz.
   by case: m {Hrec} =>[|m]; rewrite /= mod0S2I eqxx.
case: ifP => Epq Sm Sn Sq //; rewrite ?Epq //.
case: (eqVneq y1 0) => [->|y1Nz].
  by case: n m {Sm Sn Hrec} => [|m] [|n] //=; rewrite mod0S2I eqxx.
apply: Hrec; last by rewrite ltn_modS2I.
  by rewrite -ltnS (leq_trans _ Sm) // ltn_modS2I.
by rewrite -ltnS (leq_trans _ Sn) // ltn_modS2I.
Qed.

Lemma gcdS2IE x y :
  gcdS2I x y = if ('N x < 'N y)%N
    then gcdS2I (y %% x) x else gcdS2I (x %% y) y.
Proof.
case: (eqVneq x 0) => [-> | xNz].
  by rewrite mod0S2I modS2I0 gcd0S2I gcdS2I0 if_same.
case: (eqVneq y 0) => [-> | yNz].
  by rewrite mod0S2I modS2I0 gcd0S2I gcdS2I0 if_same.
rewrite /gcdS2I.
case: ltnP; rewrite (negPf xNz, negPf yNz) //=.
  move=> ltxy; rewrite ltn_modS2I (negPf xNz) //=.
  rewrite -(ltn_predK ltxy) /=; case: eqP => [->|].
    by case: ('N x) => [|[|s]]; rewrite /= modS2I0 (negPf xNz) // mod0S2I eqxx.
  move/eqP=> yxNz; rewrite (negPf xNz).
  apply: gcdS2I_recE => //; last by rewrite ltn_modS2I.
    by rewrite -ltnS (ltn_predK ltxy) (leq_trans _ ltxy) ?leqW // ltn_modS2I.
  by rewrite ltnW // ltn_modS2I.
move=> leyx; rewrite ltn_modS2I (negPf yNz) //=.
have x_gt0: ('N x > 0)%N by rewrite normS2I_gt0.
rewrite -(prednK x_gt0) /=; case: eqP => [->|].
  by case: ('N y)%N => [|[|s]]; rewrite /= modS2I0 (negPf yNz) // mod0S2I eqxx.
move/eqP=> xyNz; rewrite (negPf yNz).
apply: gcdS2I_recE => //; last by rewrite ltn_modS2I.
  by rewrite -ltnS (prednK x_gt0) (leq_trans _ leyx) // ltn_modS2I.
by rewrite ltnW // ltn_modS2I.
Qed.

Lemma gcd1S2IE y :
  gcdS2I 1 y = if ('N y == 1)%N then y else 1.
Proof.
rewrite gcdS2IE normS2I1; case: leqP => [|H].
  rewrite leq_eqVlt; case: eqP => [/eqP|/= _].
    by rewrite -dvdS2I1 => /eqP->; rewrite gcd0S2I.
  rewrite ltnS leqn0 normS2I_eq0 => /eqP->.
  by rewrite modS2I0 gcdS2I0.
rewrite modS2I1 gcd0S2I.
by move: H; rewrite ltnNge leq_eqVlt negb_or => /andP[/negPf->].
Qed.

Lemma gcd1S2I_norm y : 'N(gcdS2I 1 y) = 1%N.
Proof. by rewrite gcd1S2IE; case: eqP; rewrite ?normS2I1. Qed.

Lemma gcdS2I1 y : gcdS2I y 1 = 1.
Proof.
rewrite gcdS2IE normS2I1; case: leqP => [_|].
  by rewrite modS2I1 gcd0S2I.
rewrite ltnS leqn0 normS2I_eq0 => /eqP->.
by rewrite modS2I0 gcdS2I0.
Qed.

Lemma gcdS2Ixx : idempotent_op gcdS2I.
Proof. by move=> x; rewrite gcdS2IE ltnn modS2Ixx gcd0S2I. Qed.

Lemma dvdS2I_mod d x y : d %| x -> (d %| y) = (d %| y %% x).
Proof.
case: (altP (x =P 0)) => [-> | nZx]; first by rewrite modS2I0.
case: (altP (d =P 0)) => [-> | nZd /dvdS2IP[q1 ->]].
  by rewrite dvd0S2I => /eqP->; rewrite modS2I0.
apply/dvdS2IP/dvdS2IP=> [] [q2 Hq2].
  rewrite /modS2I Hq2 !mulrA -mulrBl.
  by set u := _ - _; exists u.
rewrite (divS2I_eq y (q1 * d)) Hq2 mulrA -mulrDl.
by set u := _ + _; exists u.
Qed.

Lemma dvdS2I_gcdlr x y : (gcdS2I x y %| x) && (gcdS2I x y %| y).
Proof.
elim: {x y}minn {-2}x {-2}y (leqnn (minn ('N y) ('N x))) => [x y|r IH x y].
  rewrite geq_min !leqn0 !normS2I_eq0.
  by case/pred2P=>->; 
     rewrite (gcd0S2I, gcdS2I0) dvdS2Ixx ?andbT dvdS2I0.
case: (eqVneq x 0) => [-> _|nZx].
  by rewrite gcd0S2I dvdS2Ixx andbT dvdS2I0.
case: (eqVneq y 0) => [->|nZy].
  by rewrite gcdS2I0 dvdS2Ixx /= dvdS2I0.
rewrite gcdS2IE minnC /minn; case: ltnP => [lt_xy | le_xy] le_yr.
  suffices /IH/andP[E1 E2]: (minn ('N x) ('N (y %% x)%S2I) <= r)%N.
    by rewrite E2 (dvdS2I_mod _ E2).
  by rewrite geq_min orbC -ltnS (leq_trans _ le_yr) ?ltn_modS2I.
suffices /IH/andP[E1 E2] : (minn ('N y) ('N (x %% y)%S2I) <= r)%N.
  by rewrite E2 andbT (dvdS2I_mod _ E2).
by rewrite geq_min orbC -ltnS (leq_trans _ le_yr) ?ltn_modS2I.
Qed.

Lemma dvdS2I_gcdl x y : gcdS2I x y %| x.
Proof. by case/andP: (dvdS2I_gcdlr x y). Qed.

Lemma dvdS2I_gcdr x y : gcdS2I x y %| y.
Proof. by case/andP: (dvdS2I_gcdlr x y). Qed.

Lemma gcdS2I_eq0 x y : (gcdS2I x y == 0) = ((x == 0) && (y == 0)).
Proof.
have [/eqP->|/eqP nZx] := boolP (x == 0).
  by rewrite gcd0S2I.
have := dvdS2I_gcdl x y.
by case:eqP => //->; rewrite dvd0S2I => /eqP.
Qed.

Lemma dvdS2I_leq x y : y != 0 -> x %| y -> ('N x <= 'N y)%N.
Proof.
move=> nZy /dvdS2IP[q qE]; have := nZy.
rewrite qE -normS2I_eq0 normS2IM muln_eq0 negb_or => /andP[H1 H2].
by rewrite -[X in (X <= _)%N] mul1n leq_pmul2r lt0n.
Qed.

Lemma leq_gcdS2Il (x y : S2I) : x != 0 -> ('N (gcdS2I x y) <= 'N x)%N.
Proof. by move=> nZx;  apply: dvdS2I_leq => //; exact: dvdS2I_gcdl. Qed.

Lemma leq_gcdS2Ir (x y : S2I) : y != 0 -> ('N (gcdS2I x y) <= 'N y)%N.
Proof. by move=> nZy; move: (dvdS2I_gcdr x y); apply: dvdS2I_leq. Qed.

Lemma dvdS2I_trans : transitive dvdS2I.
Proof.
move=> x y z /dvdS2IP[qx -> /dvdS2IP[qy ->]].
by apply/dvdS2IP; exists (qy * qx); rewrite mulrA.
Qed.

Lemma dvdS2I_gcd x y z : x %| gcdS2I y z = (x %| y) && (x %| z).
Proof.
apply/idP/andP=> [dv_xyz | [dv_xy dv_xz]].
  by rewrite ?(dvdS2I_trans dv_xyz) ?dvdS2I_gcdl ?dvdS2I_gcdr.
move: (leqnn (minn ('N z) ('N y))) dv_xy dv_xz.
elim: {y z}minn {-2}y {-2}z => [|r IH] y z.
  rewrite geq_min !leqn0 !normS2I_eq0.
  by case/pred2P=> ->; rewrite ?(gcd0S2I, gcdS2I0).
case: (eqVneq y 0) => [-> _|nZy]; first by rewrite gcd0S2I.
case: (eqVneq z 0) => [->|nZz]; first by rewrite gcdS2I0.
rewrite gcdS2IE minnC /minn; case: ltnP => Czy le_r dv_y dv_z.
  apply: IH => //; last by rewrite -(dvdS2I_mod _ dv_y).
  by rewrite geq_min orbC -ltnS (leq_trans _ le_r) ?ltn_modS2I.
apply: IH => //; last by rewrite -(dvdS2I_mod _ dv_z).
by rewrite geq_min orbC -ltnS (leq_trans _ le_r) ?ltn_modS2I.
Qed.

Lemma dvdS2I_mul2r (p d x : S2I) :  p != 0 ->  (d * p %| x * p) = (d %| x).
Proof.
move=> nZp; apply/dvdS2IP/dvdS2IP=> [] [q Hq]; exists q.
  by apply: (mulIf nZp); rewrite -mulrA.
by rewrite Hq mulrA.
Qed.

Lemma dvdS2I_mul2l (p d x : S2I) :  p != 0 ->  (p * d %| p * x) = (d %| x).
Proof. by rewrite ![p *_]mulrC; exact: dvdS2I_mul2r. Qed.

Definition lcmS2I x y := (x * y) %/ gcdS2I x y.

Lemma mulS2I_lcm_gcd x y : lcmS2I x y * gcdS2I x y = x * y.
Proof. by apply/eqP; rewrite divS2IK // dvdS2I_mull // dvdS2I_gcdr. Qed.

Lemma lcm0S2I y : lcmS2I 0 y = 0.
Proof. by rewrite /lcmS2I mul0r div0S2I. Qed.

Lemma lcmS2I0 x : lcmS2I x 0 = 0.
Proof. by rewrite /lcmS2I mulr0 div0S2I. Qed.

Lemma lcmS2I_eq0 x y : (lcmS2I x y == 0) = ((x == 0) || (y == 0)).
Proof.
have [/eqP->|nZx] := boolP (x == 0).
  by rewrite lcm0S2I eqxx.
have [/eqP->|nZy] := boolP (y == 0).
  by rewrite lcmS2I0 eqxx.
rewrite /lcmS2I.
have /dvdS2IP[q Hq]: gcdS2I x y %| x * y by rewrite dvdS2I_mulr // dvdS2I_gcdl.
rewrite Hq divS2IKl ?gcdS2I_eq0 ?negb_and ?nZx //.
case: eqP Hq => // -> /eqP.
by rewrite mul0r mulf_eq0 (negPf nZx) (negPf nZy).
Qed.

Definition eqS2I x y :=  (dvdS2I x y) && (dvdS2I y x).

Lemma eqS2Ixx : reflexive eqS2I.
Proof. by move=> x; rewrite /eqS2I dvdS2Ixx. Qed.

Lemma eqS2I_sym : symmetric eqS2I.
Proof. by move=> x y; rewrite /eqS2I andbC. Qed.

Lemma eqS2I_trans : transitive eqS2I.
Proof. 
move=> x y z /andP[U1 V1] /andP[U2 V2].
by rewrite /eqS2I (dvdS2I_trans U1) // (dvdS2I_trans V2).
Qed.

Infix "%=" := eqS2I : S2I_scope.

Lemma eqS2I0 (x : S2I) : (x %= 0) = (x == 0).
Proof.
apply/andP/eqP=>[[]|->]; last by rewrite dvdS2Ixx.
by rewrite dvd0S2I => _ /eqP.
Qed.

Lemma eqS2I_eq0  x y : x %= y -> (x == 0) = (y == 0).
Proof.
have [/eqP->|] := boolP (x == 0).
  by rewrite eqS2I_sym eqS2I0.
have [/eqP->|//] := boolP (y == 0).
by rewrite eqS2I0 => /negP.
Qed.

Lemma eqS2I_norm  x y : x %= y -> 'N x = 'N y.
Proof.
have [/eqP->|nZx] := boolP (x == 0).
  by rewrite eqS2I_sym eqS2I0 => /eqP->.
have [/eqP->|nZy] := boolP (y == 0).
  by rewrite eqS2I0 => /eqP->.
case/andP => /(dvdS2I_leq nZy) H1 /(dvdS2I_leq nZx) H2.
by apply/eqP; rewrite eqn_leq H1.
Qed.

Lemma dvdS2I_eq_norm x y : 'N x = 'N y -> x %| y -> x %= y.
Proof.
have [/eqP->|nZx] := boolP (x == 0).
  by rewrite dvd0S2I => _ /eqP->; exact: eqS2Ixx.
move=> xNy xDy; rewrite /eqS2I xDy /=.
case/dvdS2IP: xDy => q Hq.
apply/dvdS2IP; exists q^-1.
rewrite Hq mulrA mulVr ?mul1r // -normS2I_unit.
have /eqn_pmul2r<- : (0 < 'N x)%N.
  by move: nZx; rewrite -normS2I_eq0; case: ('N x).
by rewrite -normS2IM -Hq xNy mul1n.
Qed.

Lemma eqS2I_nat m n : m%:R %= n%:R -> m = n.
Proof.
move=> /andP[H1 H2]; apply/eqP.
by rewrite -(eqn_exp2r _ _ (isT : 0 < 2)%N) -!normS2I_nat eqn_dvd !dvdS2I_norm.
Qed.

Lemma conjS2I_gcd x y : conjS2I (gcdS2I x y) %= gcdS2I (conjS2I x) (conjS2I y).
Proof.
rewrite /eqS2I dvdS2I_gcd !conjS2I_dvd //= ?(dvdS2I_gcdr,dvdS2I_gcdl) //.
rewrite -[X in X %|_]conjS2IK.
by rewrite conjS2I_dvd // dvdS2I_gcd -{2}[x]conjS2IK -{3}[y]conjS2IK !conjS2I_dvd //
          ?(dvdS2I_gcdr,dvdS2I_gcdl).
Qed. 

Lemma conjS2IM_norm x : x * conjS2I x = (s2intA x ^+ 2 - 2%:R * s2intB x ^+ 2 )%:~R.
Proof.
apply/val_eqP; rewrite /= /conjs2i /=.
have /eqP/= {1}-> := algS2IP x.
rewrite -mulNr  mulS2I_rect !mulrN.
rewrite [X in -X + _]mulrC addNr mul0r addr0 -mulrA.
by rewrite -mulrz_nat -!rmorphM -rmorphB /= -!expr2 algS2I_int.
Qed.

Lemma eqS2IP (x y : S2I) :
  reflect (exists2 u, normS2I u = 1%N & x = u * y)
          (x %= y).
Proof.
apply: (iffP andP)=> [[xDy yDx]|[u Nu->]]; last first.
  split; apply/dvdS2IP; last by exists u.
  have := conjS2IM_norm u; set z := (_ - _) => Hz.
  exists (((-1) ^ (z < 0))%:~R * (conjS2I u)).
  rewrite -!mulrA [_ * (u * _)]mulrA [_ * u]mulrC Hz mulrA.
  by rewrite -intrM -abszEsign -normS2IEAB Nu mul1r.
have: 'N x = 'N y by rewrite (@eqS2I_norm x y) ///eqS2I xDy.
case/dvdS2IP: yDx => u -> /eqP.
rewrite normS2IM -{2}['N y]mul1n eqn_mul2r normS2I_eq0 => /orP[/eqP->|/eqP Nu].
  by exists 1; rewrite ?mulr0 // normS2I1.
by exists u.
Qed.

Lemma gcdS2IC x y : gcdS2I x y %= gcdS2I y x.
Proof. by rewrite /eqS2I !(dvdS2I_gcd, dvdS2I_gcdl, dvdS2I_gcdr). Qed.

Lemma gcd1S2I y : gcdS2I 1 y %= 1.
Proof.
rewrite /eqS2I dvd1S2I dvdS2I1 gcd1S2IE.
by case: (@eqP _ ('N y) 1%N) => [->|]; rewrite ?normS2I1.
Qed.

Lemma eqS2I_dvdr x y1 y2 : y1 %= y2 -> (x %| y1) = (x %| y2).
Proof.
move=> /andP[y1Dy2 y2Dy1]; apply/idP/idP.
  by move=> /dvdS2I_trans /(_ y1Dy2).
by move=> /dvdS2I_trans /(_ y2Dy1).
Qed.

Lemma eqS2I_dvdl y x1 x2 : x1 %= x2 -> (x1 %| y) = (x2 %| y).
Proof.
move=> /andP[x1Dx2 x2Dx1]; apply/idP/idP.
  by move=> /(dvdS2I_trans x2Dx1).
by move=> /(dvdS2I_trans x1Dx2).
Qed.

Lemma eqS2I_gcdr x y1 y2 : y1 %= y2 -> gcdS2I x y1 %= gcdS2I x y2.
Proof.
move=> y1Ey2; rewrite /eqS2I !(dvdS2I_gcd, dvdS2I_gcdl, dvdS2I_gcdr).
by rewrite -(eqS2I_dvdr _ y1Ey2) dvdS2I_gcdr (eqS2I_dvdr _ y1Ey2) dvdS2I_gcdr.
Qed.

Lemma eqS2I_gcdl y x1 x2 : x1 %= x2 -> gcdS2I x1 y %= gcdS2I x2 y.
Proof.
move=> x1Ex2; apply: eqS2I_trans (gcdS2IC _ _).
by apply: eqS2I_trans (gcdS2IC _ _) _; exact: eqS2I_gcdr.
Qed.

Lemma eqS2I_mul2r (r p q : S2I) : r != 0 -> (p * r %= q * r) = (p %= q).
Proof. by move => nZr; rewrite /eqS2I !dvdS2I_mul2r. Qed.

Lemma eqS2I_mul2l (r p q : S2I): r != 0 -> (r * p %= r * q) = (p %= q).
Proof. by move => nZr; rewrite /eqS2I !dvdS2I_mul2l. Qed.

Lemma eqS2I_mul (p1 p2  q1 q2 : S2I) : 
 p1 %= q1 ->  p2 %= q2 ->  p1 * p2 %= q1 * q2.
Proof.
move=> /andP[E1 E2] /andP[F1 F2]; apply/andP; split.
  have /dvdS2IP[u1->] := E1; have /dvdS2IP[v1->] := F1.
  by apply/dvdS2IP; exists (u1 * v1); rewrite mulrAC [p1 * _]mulrC !mulrA.
have /dvdS2IP[u1->] := E2; have /dvdS2IP[v1->] := F2.
by apply/dvdS2IP; exists (u1 * v1); rewrite mulrAC [q1 * _]mulrC !mulrA.
Qed.

Fixpoint egcdS2I_rec n (x y : S2I) := 
  if y == 0 then (1, 0) else
  if n is n1.+1 then
    let: (u, v) := egcdS2I_rec n1 y (modS2I x y) in
     (v, u - v * (x %/ y)%S2I)
  else (1, 0).

Definition egcdS2I (x y : S2I) :=
  if ('N y <= 'N x)%N then 
    egcdS2I_rec ('N x) x y else
  let e := egcdS2I_rec ('N y) y x in (e.2, e.1).

Lemma egcdS2I_rec0r n x : egcdS2I_rec n x 0 = (1, 0).
Proof. by case: n => /= [|n]; rewrite eqxx. Qed.

Lemma egcdS2I0 x : egcdS2I x 0 = (1, 0).
Proof.  by rewrite /egcdS2I normS2I0 egcdS2I_rec0r. Qed.

Lemma egcd0S2I y : y != 0 -> egcdS2I 0 y = (0, 1).
Proof.
by rewrite /egcdS2I normS2I0 -normS2I_eq0 leqn0  egcdS2I_rec0r => /negPf->/=.
Qed.

Lemma egcdS2I_recP : 
  forall n x y,  y != 0 -> ('N y <= n)%N -> ('N y <= 'N x)%N ->
  forall (e := egcdS2I_rec n x y), gcdS2I_rec n x y = e.1 * x + e.2 * y.
Proof.
elim => [x y nZy|n /= IH x y nZy NyLn NyLNx].
  by rewrite leqn0 normS2I_eq0 (negPf nZy).
have NxP : (0 < 'N x)%N.
  by apply: leq_trans NyLNx; rewrite ltnNge leqn0 normS2I_eq0.
rewrite (negPf nZy).
have [r0|nZr0] := eqVneq (x %% y) 0.
  by rewrite r0 egcdS2I_rec0r !mul0r subr0 add0r mul1r.
have NxyLn : ('N(x %% y)%S2I <= n)%N.
  by rewrite -ltnS (leq_trans _ NyLn) // ltn_modS2I.
have NxyLNy : ('N (x %% y)%S2I <= 'N y)%N by rewrite ltnW // ltn_modS2I.
have := IH _ _ nZr0 NxyLn NxyLNy.
case: (egcdS2I_rec _ _) => u v ->.
by rewrite /= /modS2I mulrBr mulrBl addrCA mulrA.
Qed.

Lemma egcdS2IP (x y : S2I) : gcdS2I x y = (egcdS2I x y).1 * x + (egcdS2I x y).2 * y.
Proof.
have [->|nZy] := eqVneq y 0.
  by rewrite egcdS2I0 gcdS2I0 mul1r mulr0 addr0.
have [->|nZx] := eqVneq x 0.
  by rewrite mulr0 add0r gcd0S2I egcd0S2I // mul1r.
rewrite /egcdS2I /gcdS2I.
case: leqP => [H|H] /=; last first.
  rewrite (negPf nZy) addrC.
  by apply: egcdS2I_recP; rewrite // ltnW.
rewrite (negPf nZx).
apply: egcdS2I_recP => //.
Qed.

Lemma mulS2I_gcdr x y z : x * gcdS2I y z %= gcdS2I (x * y) (x * z).
Proof.
have [/eqP->|nZx] := boolP (x == 0); first by rewrite !mul0r gcd0S2I eqS2Ixx.
rewrite /eqS2I dvdS2I_gcd !dvdS2I_mul2l // dvdS2I_gcdl dvdS2I_gcdr /=.
rewrite [X in _%|_ * X]egcdS2IP mulrDr dvdS2I_add // mulrCA dvdS2I_mull //.
  by rewrite dvdS2I_gcdl.
by rewrite dvdS2I_gcdr.
Qed.

Lemma mulS2I_gcdl x y z : gcdS2I y z * x %= gcdS2I (y * x) (z * x).
Proof. by rewrite ![_ * x]mulrC mulS2I_gcdr. Qed.

Lemma dvdS2I_lcm d1 d2 x : lcmS2I d1 d2 %| x = (d1 %| x) && (d2 %| x).
Proof.
have [/eqP->|nZd1] := boolP (d1 == 0).
  by rewrite lcm0S2I dvd0S2I; case: eqP => //->; rewrite dvdS2I0.
have [/eqP->|nZd2] := boolP (d2 == 0).
  by rewrite lcmS2I0 dvd0S2I andbC; case: eqP=> //->; rewrite dvdS2I0.
have /dvdS2I_mul2r<- : gcdS2I d1 d2 != 0 by rewrite gcdS2I_eq0 negb_and nZd1.
rewrite mulS2I_lcm_gcd (eqS2I_dvdr _ (mulS2I_gcdr _ _ _)) dvdS2I_gcd.
by rewrite {1}mulrC !dvdS2I_mul2r // andbC.
Qed.

Definition oddz (z : int) := odd `|z|.

Lemma oddzN z : oddz (-z) = oddz z.
Proof. by rewrite /oddz abszN. Qed. 

Lemma oddzD z1 z2 : oddz (z1 + z2) = oddz z1 (+) oddz z2.
Proof.
case: z1; case: z2 => n1 n2; rewrite /oddz /= ?NegzE ?oddD //; last first.
- by case: odd; rewrite /= negbK.
- rewrite addrC.
  have [H|H] := leqP n1 n2.+1; first by rewrite distnEr // oddB.
  by rewrite distnEl ?(leq_trans _ H) // oddB 1?addbC // ?(leq_trans _ H) .
have [H|H] := leqP n2 n1.+1; first by rewrite distnEr // oddB // addbC.
by rewrite distnEl ?(leq_trans _ H) // oddB 1?addbC // ?(leq_trans _ H) .
Qed.

Lemma oddzM z1 z2 : oddz (z1 * z2) = oddz z1 && oddz z2.
Proof. by rewrite /oddz abszM oddM. Qed.

Lemma oddzN_div z : ~~ oddz z -> exists z1 : int, z = 2%:R * z1.
Proof.
wlog /gez0_abs<- : z / 0 <= z => [H Oz|Oz].
  have [/H/(_ Oz)[q ->]|H2] := lerP 0 z; first by exists q.
  rewrite -[z]opprK.
  case: (H (-z))=> [||q->]; first by rewrite oppr_ge0 ltW.
    by rewrite oddzN.
  by exists (-q); rewrite mulrN.
exists (Posz `|z|./2).
by rewrite -PoszM /oddz mul2n -{1}[`|z|%N]odd_double_half [odd _](negPf Oz).
Qed.

Definition odds2i x := oddz (s2intA x).
Definition odds2j x := oddz (s2intB x).

Lemma odds2iN (x : algC):  x \is a s2Int -> odds2i (- x ) = odds2i x.
Proof. by move=> xS; rewrite /odds2i s2intAN // oddzN. Qed.

Lemma odds2iD (x y : algC): 
  x \is a s2Int -> y \is a s2Int -> odds2i (x + y) = odds2i x (+) odds2i y.
Proof. by move=> xS yS; rewrite /odds2i s2intA_add // oddzD. Qed.

Lemma odds2iM (x y : algC) :
  x \is a s2Int -> y \is a s2Int -> odds2i (x * y) = odds2i x && odds2i y.
Proof. by move=> xS yS; rewrite /odds2i s2intA_mul // oddzD 3!oddzM addbF. Qed.

Lemma odds2i_conj (x : algC) : x \is a s2Int -> odds2i (x^*) = odds2i x.
Proof.  by move=> xS; rewrite conj_Creal // Creal_s2Int. Qed.

Lemma odds2i_sQ2 : ~~ odds2i (sqrtC 2%:R).
Proof.
rewrite /odds2i -[sqrtC _]mul1r s2intA_sqrt ?rpred1 //.
by rewrite (s2intB_nat 1) mulr0.
Qed.

Lemma odds2i_dvd (x : S2I) : ~~ odds2i x = (sQ2 %| x).
Proof.
apply/idP/dvdS2IP=> [/oddzN_div[q Hq]|[q->]]; last first.
  rewrite rmorphM odds2iM  //=; last by have := algS2IP sQ2.
  have /eqP := algS2IP x.
  by rewrite (negPf odds2i_sQ2) andbF.
pose r : algC := (s2intB x)%:~R + q%:~R * sqrtC 2%:R.
have rO : r \is a s2Int by rewrite divS2I_subproof.
exists (S2Iof rO).
apply/val_eqP=> /=.
have /eqP-> := algS2IP x.
rewrite /= /r Hq [(_ + _) * sqrtC _]mulrDl addrC -mulrA.
by rewrite -expr2 sqrtCK [2%:R * _]mulrC [(q * _)%:~R]intrM.
Qed.

Lemma odds2jN (x : algC):  x \is a s2Int -> odds2j (- x ) = odds2j x.
Proof. by move=> xS; rewrite /odds2j s2intBN // oddzN. Qed.

Lemma odds2jD (x y : algC): 
  x \is a s2Int -> y \is a s2Int -> odds2j (x + y) = odds2j x (+) odds2j y.
Proof. by move=> xS yS; rewrite /odds2j s2intB_add // oddzD. Qed.

Lemma odds2jM (x y : algC) :
  x \is a s2Int -> y \is a s2Int -> 
  odds2j (x * y) = (odds2i x && odds2j y) (+) (odds2j x && odds2i y).
Proof. 
by move=> xS yS; rewrite /odds2i /odds2j s2intB_mul // oddzD 2!oddzM.
Qed.

Lemma odds2j_conj (x : algC) : x \is a s2Int -> odds2j (x^*) = odds2j x.
Proof.  by move=> xS; rewrite conj_Creal // Creal_s2Int. Qed.

Lemma odds2j_sQ2 : odds2j (sqrtC 2%:R).
Proof.
by rewrite /odds2j -[sqrtC _]mul1r s2intB_sqrt ?rpred1 // (s2intA_nat 1).
Qed.

Lemma odds2ij_dvd (x : S2I) : ~~ (odds2i x || odds2j x) = (2%:R %| x).
Proof.
rewrite negb_or.
apply/idP/dvdS2IP=>[/andP[/oddzN_div[p Hp] /oddzN_div[q Hq]]|[q ->]].
  pose r : algC := p%:~R + q%:~R * sqrtC 2%:R.
  have rO : r \is a s2Int by rewrite divS2I_subproof.
  exists (S2Iof rO); apply/val_eqP=>/=.
  have /eqP-> := algS2IP x.
  by rewrite Hp Hq !rmorphM /= -!mulrA -mulrDr mulrC.
rewrite !(odds2iM, odds2jM) //.
rewrite {2}/odds2i (s2intA_nat 2) andbF /=.
rewrite {1}/odds2j (s2intB_nat 2) andbF /=.
by rewrite /odds2i (s2intA_nat 2) andbF.
Qed.

Lemma odds2iE x : x \is a s2Int -> odds2i x = odds2j (x * sqrtC 2%:R).
Proof.
move=> xIs.
rewrite odds2jM ?sQ2_proof //.
by rewrite odds2j_sQ2 (negPf (odds2i_sQ2)) andbF addbF andbT.
Qed.

Lemma odds2i_nat n : odds2i n%:R = odd n.
Proof. by rewrite /odds2i s2intA_nat /oddz natz. Qed.

Lemma odds2i_sum (I : eqType) (r : seq _) (P : pred I) E :
  (forall i, i \in r -> P i -> E i \is a s2Int) ->
  odds2i (\sum_(i <- r | P i) E i) = \big[addb/false]_(i <- r | P i) odds2i (E i).
Proof.
elim: r => [H|a r IH H]; first by rewrite !big_nil (odds2i_nat 0).
have  H1 i :  i \in r -> P i -> E i \is a s2Int.
  by move=> Hi Pi; rewrite H // in_cons Hi orbT.
have IH1 := IH H1.
rewrite !big_cons; case H2 : (P a) => //.
rewrite odds2iD ?IH1 //; first by rewrite H// in_cons eqxx.
by rewrite big_seq_cond rpred_sum // => i /andP[Hi Pi]; rewrite H1.
Qed.


End S2int.

Declare Scope S2I_scope.
Delimit Scope S2I_scope with S2I.

Notation "'N x" := (normS2I x%R) (at level 10) : S2I_scope.
Notation " x %| y " := (dvdS2I x y) : S2I_scope.
Notation " x %/ y " := (divS2I x y) : S2I_scope.
Notation " x %% y " := (modS2I x y) : S2I_scope.
Notation " x %= y " := (eqS2I x y) : S2I_scope.

