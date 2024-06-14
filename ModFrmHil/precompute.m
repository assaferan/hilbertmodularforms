// copy pasted from precompute.m and modified

// Given a sequence of units in OF that form a subgroup U of OF*/(OF*)^2 
// containing N meet Kernel(eps), where N is the group of norms of OH*, this returns units in OF 
// whose images in OF*/(OF*)^2 form a transversal of U/(N meet Ker(eps))

function units_mod_norms(units, OH : hack := true, eps := 1)
  OF := BaseRing(OH);
  UF, unitmap := UnitGroup(OF);
  UFmod2, mod2 := quo< UF | 2*UF >;
  norms := {Norm(u) : u in Units(OH)};
  // hack begins
  if hack then
      if IsOne(eps) then
	  eps := TrivialCharacter(NumberField(OF));
      end if;
      N := sub< UFmod2 | [u @@unitmap @mod2 : u in norms | eps(u) eq 1] >;
  else
      N := sub< UFmod2 | [u @@unitmap @mod2 : u in norms] >;
  end if;
  // hack ends
  U := sub< UFmod2 | [u @@unitmap @mod2 : u in units] >;
  assert N subset U;
  return [t @@mod2 @unitmap : t in Transversal(U,N)];
end function;


////////////////////////   PRECOMPUTATION   ///////////////////////////

// Let I1, .., Ih denote the ridls.  For a prime power P = PP^eP,
// tps[<j,i>] := sequence of reps t in A, up to units of LeftOrder(Ii)
// such that P*Ii < t*Ij < Ii and the size of (t*Ij)\Ii is Norm(P)^2
// (Note that when eP > 1, we don't remove the "non-Hecke elements" here)

procedure precompute_tps_unit_character(OH, P, ridls, record_idx, rows : hack := true, eps := eps)

    H := Algebra(OH);
    F := BaseField(H);  
    OF := Integers(F);
  
    Pfact := Factorization(P);
    assert #Pfact eq 1; // must be prime power
    PP, eP := Explode(Pfact[1]);
    NP := Norm(P);
    NPP := Norm(PP);
    ramified := P in RamifiedPlaces(H);
    assert eP eq 1 or not ramified;
    if ramified then
	num := 1;
    elif eP eq 1 then
	num := NP + 1;
    else
	NPP := Norm(PP);
	num := (NPP^(eP+1) - 1) div (NPP - 1);
    end if;

    h := #ridls;
    assert rows subset [1..h];

    // TO DO: distinct left orders may be isometric, when Disc(H) ne 1
    // (it's unavoidable if we insist on strict_support in get_rids).
    // It just means redundant work computing thetas, norm_one_units etc
    ords := [];
    order_indices := [];
    for I in ridls do 
	for i := 1 to #ords do
	    if IsIdentical(ords[i], I`LeftOrder) then 
		Append(~order_indices, i); 
		continue I; 
	    end if;
	end for;
	Append(~ords, I`LeftOrder);
	Append(~order_indices, #ords); 
    end for;

    vprintf ModFrmHil: "Precomputation" * (debug select " (in debug mode): " else ": ") * "\n";
    IndentPush();
    time0 := Cputime();
    vprint ModFrmHil, 3: "Left order classes of the right ideal classes are", order_indices;
    
    pos_units := TotallyPositiveUnits(OF);
    for l := 1 to #ords do 
	LO := ords[l];
	if not assigned LO`norm_one_units_mod_scalars then
	    n1group, n1map := NormOneGroup(LO : ModScalars);
	    LO`norm_one_units_mod_scalars := [u@n1map : u in n1group];
	end if;
	if not assigned LO`pos_scalar_units_mod_norms then
	    LO`pos_scalar_units_mod_norms := units_mod_norms(pos_units, LO : hack := hack, eps := eps);
	end if;
    end for;
    pos_units_mod_norms := [LeftOrder(I)`pos_scalar_units_mod_norms : I in ridls];
    real_places := RealPlaces(F);
    U, Umap := IndependentUnits(OF);
    Uvals := [RealValuations(RealPlaces(F), Umap(U.i)) : i in [1..Ngens(U)]]; 
    UnitRealValuations := <U, Umap, Uvals>;
    
    // Decide whether to use small prime method for the prime P, 
    // and whether it's worth using thetas
    // TO DO: rethink this -- if the colons etc are known, the large prime method is very quick,
    //        at least until the field degree gets too large.  A nice example is Q(sqrt(82)).
    C := #NarrowClassGroup(F); // known
    use_theta := h gt 10 and #ords gt 1  // could be worthwhile 
		 and rows eq [1..h];     // TO DO for arbitrary rows(?)
    small_prime := eP eq 1; // subideals code assumes P is prime
    small_prime and:= ramified or
		      use_theta select 10*num le #rows/C // would be 1*num if thetas distinguished all orders, and ignoring all overhead
		      else h/2*num le #rows/C;
    use_theta and:= small_prime; // only the small_prime method involves thetas
    
    if not assigned OH`RightIdealClasses[record_idx]`rids_narrow_class_junk then
	ClF, ClFmap := NarrowClassGroup(F);
	ClFelts := [ cl : cl in ClF ];
	ClFreps := [ cl @ClFmap : cl in ClFelts ]; assert ClFreps[1] eq 1*OF;
	ridls_norms_classes := [Norm(I) @@ClFmap : I in ridls];
	inds := [Index(ClFelts, NI) : NI in ridls_norms_classes];

	// For each pair of ridls I,J find a generator of the pid R*Norm(I)/Norm(J) where R is in ClFreps 
	ridls_norms_gens       :=  [F| 0 : i in [1..h]];
	ridls_colon_norms_gens := [[F| 0 : i in [1..h]] : j in [1..h]];
	ClF_reps_diffs_gens    := [[F| 0 : i in [1..#ClFreps]] : j in [1..#ClFreps]];
	// Find generators of Cij/rep(Cij) where Cij is rep[i]/rep[j]
	for j,i in Seqset(inds) do 
	    if i eq j then
		ClF_reps_diffs_gens[j][i] := F!1;
	    else
		Q := ClFreps[i]/ClFreps[j];
		R := ClFreps[r] where r is Index(ClFelts, ClFelts[i]-ClFelts[j]);
		_, g := IsNarrowlyPrincipal(Q/R : real_places:=real_places, UnitRealValuations:=UnitRealValuations);
		ClF_reps_diffs_gens[j][i] := F!g;
	    end if;
	end for;
	vprintf ModFrmHil: "Computing generators for norms of right ideal classes ... "; 
	// vtime ModFrmHil:
	for i := 1 to h do 
	    ii := Index(ClFelts, -ridls_norms_classes[i]);
	    _, g := IsNarrowlyPrincipal(ClFreps[ii]*Norm(ridls[i]) : real_places:=real_places, 
								     UnitRealValuations:=UnitRealValuations);  
	    ridls_norms_gens[i] := F!g;
	end for;
	for j,i in [1..h] do
	    ii := Index(ClFelts, -ridls_norms_classes[i]);
	    jj := Index(ClFelts, -ridls_norms_classes[j]);
	    ridls_colon_norms_gens[j][i] := (i eq j) select 1 else
					    ridls_norms_gens[i]/ridls_norms_gens[j] / ClF_reps_diffs_gens[jj][ii];
	end for;
if debug then // check by doing it the straightforward O(h^2) way 
    for j,i in [1..h] do 
        R := ClFreps[r] where r is Index(ClFelts, ridls_norms_classes[j]-ridls_norms_classes[i]);
        bool, g := IsNarrowlyPrincipal(R*Norm(ridls[i])/Norm(ridls[j]) : real_places:=real_places,
                                                                         UnitRealValuations:=UnitRealValuations);  
        assert bool and g*OF eq g1*OF where g1 is ridls_colon_norms_gens[j][i];
    end for; 
end if;

OH`RightIdealClasses[record_idx]`rids_narrow_class_junk := 
    [* ClF, ClFmap, ClFelts, ClFreps, ridls_norms_classes, inds, ridls_norms_gens, ridls_colon_norms_gens *];
end if; // assigned junk
// Look up junk
ClF, ClFmap, ClFelts, ClFreps, ridls_norms_classes, _, _, ridls_colon_norms_gens 
:= Explode(OH`RightIdealClasses[record_idx]`rids_narrow_class_junk);

if use_theta then
    // Try to quickly determine the class of the left order of each subideal using theta series.  
    // This reduces the number of ideal-isomorphism tests, but means we have to compute the left orders + thetas. 
    ords_forms := [ [j[2],j[3]] where j is junk_for_IsIsomorphic(LO) : LO in ords ];
    /* TO DO: use values of short vectors somehow ... it's yielded nothing so far!
       ords_grams := [ T*j[5]*Transpose(T) where T is Parent(j[5])!j[4] 
       where j is junk_for_IsIsomorphic(LO) : LO in ords ];
   */
    // Note: LO`thetas[1] now computed in RightIdealClassesAndOrders
    if not &and [assigned LO`thetas : LO in ords] then
	// check if the second forms are pos def (TO DO: should we arrange this by taking 'a' totally positive?)
	js := &and[ IsPositiveDefinite(forms[2]) : forms in ords_forms ] select [1,2] else [1];
	ords_lats := [ [LatticeWithGram(ords_forms[i,j] : CheckPositive:=false) : j in js] : i in [1..#ords] ];
	dim := 4*Degree(F); 
	Vol1 := Pi(RealField())^(dim/2) / Gamma(dim/2 + 1); // = volume of unit sphere of this dimension
	Det_size := Min([ Determinant(ords_forms[i][1]) : i in [1..#ords] ]);
	theta_prec := Ceiling( (100 * Sqrt(Det_size) / Vol1) ^ (2/dim) );
	g := GCD([gcd_of_quad_form(ords_forms[i,j]) : i in [1..#ords], j in js]); // lazy
	theta_prec := (theta_prec div g) * g; // TO DO: ThetaSeries should be smart enough to figure this out!
	// get theta coefficients up to and including theta_prec
	vprintf ModFrmHil: "Computing theta series to precision %o ... ", theta_prec; 
	vtime ModFrmHil:
    for i := 1 to #ords do
        ords[i]`thetas := [ThetaSeries(ords_lats[i,j], theta_prec) : j in js];
    end for;
vprint ModFrmHil, 3: "Theta series of the left orders are", &cat [LO`thetas : LO in ords];
else // need js below (this is hacky)
js := [1..#ords[1]`thetas];
assert &and [#LO`thetas eq #js : LO in ords];
end if;
ords_thetas := [LO`thetas : LO in ords];
// reset theta_prec to the minimum that distinguishes these pairs of (partial) theta series
// TO DO: haven't done it properly for pairs 
    theta_prec := 1;
    for j := 1 to #ords_thetas[1] do 
      coeffs := [ [Coefficient(th,n) : n in [1..AbsolutePrecision(th)-1]] where th is thetas[j] 
                                                                         : thetas in ords_thetas ];
      coeffs := Sort(Setseq(Seqset(coeffs))); // sort the distinct thetas lexicographically
      for k := 2 to #coeffs do 
        i := Min([i : i in [1..#coeffs[k]] | coeffs[k-1][i] ne coeffs[k][i] ]); 
        theta_prec := Max(theta_prec, i);
      end for;
    end for;
    vprintf ModFrmHil, 2: "Using theta series to precision %o (the %o orders have %o distinct series)\n", 
                           theta_prec, #ords, #Seqset(ords_thetas);
    /* Also use the values of f2 on short vectors of f1 to distinguish pairs 
    ords_short_vals := [* *];
    vprintf ModFrmHil, 1: "Listing values on short vectors ... ", theta_prec; 
    vtime ModFrmHil, 1:
    for i := 1 to #ords_forms do 
      // look at the second positive integer that is represented by the first form
      // (no point considering the first because shortest vectors are exactly the units of norm 1)
      assert theta_prec lt 2*Degree(F) or Minimum(ords_lats[i,1]) eq 2*Degree(F); // just to make sure
      N := 2*Degree(F) + 1;
      while N le theta_prec do 
        if Coefficient(ords_thetas[i,1], N) gt 0 then break; end if;
        N +:= 1;
      end while;
      if N gt theta_prec or Coefficient(ords_thetas[i,1], N) gt 100 then 
        Append( ~ords_short_vals, {});
        continue i;
      end if;
      svs := [ sgn*Matrix(sv[1]) : sv in ShortVectors(ords_lats[i,1], N), sgn in [1,-1] ];
      //Append( ~ords_short_vals, Sort([ (sv*ords_forms[i,2]*Transpose(sv))[1,1] : sv in svs ]) );
      svs_vals := [ (sv*ords_grams[i]*Transpose(sv))[1,1] where sv is ChangeRing(sv,F) : sv in svs ];
      svs_vals := { <x, #[y: y in svs_vals | y eq x] > : x in Seqset(svs_vals) }; 
      Append( ~ords_short_vals, svs_vals);
    end for; // i
ii := Min([i : i in [1..#ords] | #ords_short_vals[i] gt 0 ] cat [1]);
"The short values are (sample only): ", ords_short_vals[i]; 
    */
  end if; // use_theta

  // seems always faster to use_Jprime for the colon calculation 
  // instead of ColonInternal
  // However ... the basis obtained when we use_Jprime seems worse,
  // so the lattice enumeration step then takes longer, eg
  // around 20% longer for the real subfield of Q(zeta_25) of degree 10.
  // The enumeration cost dominates running time for degree > 8.
  use_Jprime := Degree(F) le 8; 
  if use_Jprime then  
    if debug then   // make sure ridls are integral ideals, as the Jprime trick assumes
      for J in ridls do assert &and [zb in OJ : zb in ZBasis(J)] where OJ is RightOrder(J); end for;
    end if;
    ps := LCM([NP] cat [Integers()| Norm(Norm(J)) : J in ridls ]); 
    vprintf ModFrmHil, 3: "Getting JJs ... ";  
    vtime ModFrmHil, 3:
    JJs := [ <JJ,b,P> where JJ,b,P is Jprime(J : coprime_to:=ps) : J in ridls ]; 
  end if;

    // (previously) loop over several Ps started here

    bool, tps := IsDefined(OH`RightIdealClasses[record_idx]`tps, P);
    if not bool then
      tps := AssociativeArray(CartesianProduct([1..h],[1..h]));
    end if;
      
    Pclass := P @@ ClFmap;
    Pclassrep := ClFreps[r] where r is Index(ClFelts, Pclass);
    bool, gP := IsNarrowlyPrincipal(P/Pclassrep : real_places:=real_places, 
                                    UnitRealValuations:=UnitRealValuations);  assert bool;
    gP := F!gP;
    function inds_for_j(j)
      b := ridls[j];
      NormbP := Norm(ridls[j])/P; // = Norm(bP) for each bP below
      NormbP_class := ridls_norms_classes[j] - Pclass;
      inds := [i : i in [1..h] | ridls_norms_classes[i] eq NormbP_class];
      return inds, b, NormbP, NormbP_class;
    end function;

    if eP eq 1 then
      vprintf ModFrmHil: "Getting tp's for prime of norm %o (using \"%o prime method\")\n", 
                          NP, small_prime select "small" else "large";
    else
      vprintf ModFrmHil: "Getting tp's for ideal of norm %o^%o (using \"%o prime method\")\n", 
                          NPP, eP, small_prime select "small" else "large";
    end if;
    IndentPush(); 

    if small_prime then  // quicker to run through subideals

      // Let I1, .., Ih denote the ridls.  
      // We need Ij < t^-1*Ii with norm-index P. 
      // Writing b for Ij, list the (NP+1) P-super-ideals bP of b.  
      // For each bP, find Ii and t with t*bP = Ii. 
      // Thus t is determined up to left mult by units of LeftOrder(Ii)

      for j in rows do
        inds, b, NormbP, NormbP_class := inds_for_j(j);
        vprintf ModFrmHil, 2: "Subideals"; 
        vtime ModFrmHil, 2:
        b_subideals := Subideals_of_ideal_newer(b, P : use_theta:=use_theta );
        vprintf ModFrmHil, 2: "Ideal isomorphism tests: "; time_iso := Cputime();
        numtests := 0;

        for bsub in b_subideals do 
          // Set bP := P^-1 * bsub
          bPCIs := [ Pinv*CI : CI in CoefficientIdeals(PseudoMatrix(bsub)) ] where Pinv is P^-1;
          bPmat := Matrix(PseudoMatrix(bsub));
          bP := rideal< OH | PseudoMatrix(bPCIs, bPmat) : Check:=debug >;
          if debug then assert Norm(bP) eq NormbP; 
          else bP`Norm := NormbP; end if; 
          // Figure out the class of bP as a right ideal of O
          // ie compute v in A, a in ridls such that  v*a = bP.
         /* TO DO: figure out whether this makes any sense, and fix syntax now that tps are arrays
          // Some hocus pocus to guess which inds are more likely:
          inds_nonzero := [i : i in inds | IsDefined(tps[<j,i>]) and #tps[<j,i>] gt 0]; // indices of ridls which already showed up
          if #inds_nonzero gt 0 then 
            // if some ridls tend to occur repeatedly, check those first; 
            // if they tend to occur at most once, check the others first
            avg_count := &+[#tps[<j,i>] : i in inds_nonzero] / #inds_nonzero;
            sgn := (avg_count gt 1.33 or #inds_nonzero eq 1) select 1 else -1; 
            Sort(~inds, func< i1,i2 | sgn*(#tps[<j,i2>]-#tps[<j,i1>]) >); 
          end if;
         */
          if use_theta then
            bsub_forms := [j[2],j[3]] where j is junk_for_IsIsomorphic(LeftOrder(bsub));
          //bsub_gram := T*j[5]*Transpose(T) where T is Parent(j[5])!j[4] 
          //                                 where j is junk_for_IsIsomorphic(LeftOrder(bsub)); 
            bsub_lats := [ LatticeWithGram(f : CheckPositive:=false) : f in bsub_forms[js] ];
            vprintf ModFrmHil,3: "ThetaSeries ... "; 
            vtime ModFrmHil,3:
            bsub_thetas := [ ThetaSeries(L, theta_prec) : L in bsub_lats ];
  /* skip this for now, because it doesn't help with the Gross example (or indeed any example I've seen yet!)
    assert Minimum(bsub_lats[1]) eq 2*Degree(F);
            N := 2*Degree(F) + 1;
            while N le theta_prec do 
              if Coefficient(bsub_thetas[1], N) gt 0 then break; end if;
              N +:= 1;
            end while;
            if N gt theta_prec or Coefficient(bsub_thetas[1], N) gt 100 then 
              bsub_short_vals := {};
            else
              svs := [ sgn*Matrix(sv[1]) : sv in ShortVectors(bsub_lats[1], N), sgn in [1,-1] ];
              //bsub_short_vals := Sort([ (sv*bsub_forms[2]*Transpose(sv))[1,1] : sv in svs ]);
              svs_vals := [ (sv*bsub_gram*Transpose(sv))[1,1] where sv is ChangeRing(sv,F) : sv in svs ];
              bsub_short_vals := { <x, #[y: y in svs_vals | y eq x] > : x in Seqset(svs_vals) }; 
            end if;
  */
          end if;
          found_class := false; 
          for i in inds do
            // quickly try to rule out some order classes (by looking at short vectors of the pair of forms)
            if use_theta then 
              io := order_indices[i];
              for j in js do
                if Valuation(bsub_thetas[j] - ords_thetas[io,j]) le theta_prec then 
                  continue i; 
                end if; 
              end for;
              /*
              if bsub_short_vals ne ords_short_vals[io] then
                "short vals don't match"; 
                continue i; 
              end if;
              */
            end if;
            numtests +:= 1;
            if use_Jprime then
              // scale to make ideal integral, since the Jprime trick assumes this
              bool, v := IsIsomorphicInternal(NP*bP, ridls[i] : real_places:=real_places,
                                                                UnitRealValuations:=UnitRealValuations,
                                                                JJ:=JJs[i] );
              if bool then v *:= NP; end if;
            else                                                         
              bool, v := IsIsomorphicInternal(bP, ridls[i] : real_places:=real_places,
                                                             UnitRealValuations:=UnitRealValuations );
            end if;
            if bool then
              if debug then assert ridls[i] eq v*bP; end if;
              ji := <j,i>;
              if IsDefined(tps, ji) then
                Append(~tps[ji], v); 
              else
                tps[ji] := [v]; 
              end if;
              error if found_class, "This ideal is in more than one class!!!\n", bP; // only caught in debug
              found_class := true; 
              if not debug then break i; end if;
            end if;
          end for; // i
          error if not found_class, "Failed to find isomorphism class for right ideal\n", bP;
        end for; // bsub
        vprintf ModFrmHil, 2: "needed %o tests; time for row = %o sec\n", numtests, Cputime(time_iso);

        for subI in b_subideals do  // these ideals are gonna get deleted, make sure stored data gets deleted too
         if assigned subI`LeftOrder then 
          delete subI`LeftOrder`junk_for_IsIsomorphic; end if; end for;
      
     end for; // j
   end if;
if not small_prime then  // NP large relative to h ==> quicker to run through ideal classes

      // Let I1 .. Ih denote the ridls.  For each pair Ij, Ii, we list all t in H 
      // with t*Ij < Ii and Norm(t*Ij) = P*Norm(Ii), up to mult by scalars, 
      // and then choose reps for t modulo left mult by units of LeftOrder(Ii)

       // hack begins
       if hack then
	   vals := Set(ValuesOnGens(eps));
	   ts_raw := AssociativeArray(vals);
	   for v in vals do
	       ts_raw[v] := [];
	   end for;
       else
	   ts_raw := []; // ts_raw[j] will contain raw ts for the jth row
       end if;
       // hack ends
       
       ridls_colonZBs := OH`RightIdealClasses[record_idx]`rids_colonZBs; 

       for j := 1 to h do 
           if j notin rows then
	       // hack begins
	       if hack then
		   for v in vals do
		       Append(~ts_raw[v], [[] : i in [1..h]]);
		   end for;
	       else
		   Append(~ts_raw, [[] : i in [1..h]]);
	       end if;
	       // hack ends
               continue;
           end if;

           inds := inds_for_j(j);

           // Make sure we know Z-bases for (I:J)'s
           for i in inds do 
               // Get a totally positive generator g of the ideal (there exists one, for i in inds)
               if not IsDefined(ridls_colonZBs, <j,i>) then
		   vprintf ModFrmHil,3: "Z-basis for I:J (%ousing the J' trick) ... ", 
                                        use_Jprime select "" else "not "; 
		   vtime ModFrmHil,3:
    if use_Jprime then 
        JJ, b := Explode(JJs[j]);  // [I : J] = I * J^-1 = I * JJ * b^-1
        IJJ_ZB := IntersectionZBasis(ridls[i], JJ);
              ridls_colonZBs[<j,i>] := [H| x*binv : x in IJJ_ZB ] where binv is b^-1;
    else
        icolonj := ColonInternal(PseudoMatrix(ridls[i],H), PseudoMatrix(ridls[j],H), H, true // left multipliers
                                 : Hermite:=false); 
        ridls_colonZBs[<j,i>] := ZBasis(icolonj, H);
    end if;
end if;
end for; // i in inds

        vprintf ModFrmHil, 2: "Doing row #%o:  ", j;
        time_row := Cputime();

        if debug then
          for i in inds do
            g := ridls_colon_norms_gens[j][i]*gP;
            assert g*OF eq Norm(ridls[i])/Norm(ridls[j])*P;
          end for;
        end if;

	// hack begins
	if hack then
	    vals := ValuesOnGens(eps);
	    ts_raw_j := [AssociativeArray(vals) : i in [1..h]];
	    for i in inds do
		g := ridls_colon_norms_gens[j][i] * gP;
		for u in pos_units_mod_norms[i] do
		    bool, elts := has_element_of_norm(ridls_colonZBs[<j,i>], u*g : all);
		    if bool then
			ts_raw_j[i][u] := elts; 
		    end if;
		end for;
            end for;
	else
            ts_raw_j := [[] : i in [1..h]];
            for i in inds do
		g := ridls_colon_norms_gens[j][i] * gP;
		for u in pos_units_mod_norms[i] do
		    bool, elts := has_element_of_norm(ridls_colonZBs[<j,i>], u*g : all);
		    if bool then 
			Append(~ts_raw_j[i], elts); 
		    end if;
		end for;
            end for;
	end if;
	// hack ends
        Append(~ts_raw, ts_raw_j); assert #ts_raw eq j;
       
        vprintf ModFrmHil, 2: "Time for row #%o: %o\n", j, Cputime(time_row);

      end for; // j

      OH`RightIdealClasses[record_idx]`rids_colonZBs := ridls_colonZBs; // update cache (note: this might use a lot of memory!)

      // We've computed ts_raw[j][i] for all (relevant) j and i
      // Now choose one from each orbit under left action of units

      // Choose well-defined reps mod +-1 
      function normalize(S)
        return {-s lt s select -s else s : s in S};
      end function;

      inds := [(j in rows) select inds_for_j(j) else [] : j in [1..h]];
      allinds := Seqset(&cat inds);
      noums := AssociativeArray(allinds);
      for i in allinds do 
        noumsi := ridls[i]`LeftOrder`norm_one_units_mod_scalars;
        assert Universe(noumsi) eq H;
        Exclude(~noumsi, H!1);
        Exclude(~noumsi, H!-1);
        noums[i] := noumsi;
      end for;

      vprintf ModFrmHil, 2: "Choosing representatives modulo left multiplication by units: ";
      vtime ModFrmHil, 2:

      for j in rows do
          for i in inds[j] do
	      
          ts := [H| ];
          for ie := 1 to #ts_raw[j][i] do 
            elts := ts_raw[j][i][ie]; 
            us := noums[i];
            // Discard repeats modulo left mult by the norm-one-units us;
            // here elts contains full orbits mod +-1,
            // and us are the units mod +-1
            length := 1+#us;
            if length eq 1 then
              ts cat:= elts;
            elif #elts eq length then
              Append(~ts, elts[1]);
            else
              elts := normalize(elts);
              while true do
                // assert #elts ge length;
                // assert #elts mod length eq 0;
                e1 := Rep(elts);
                Append(~ts, e1);
                if #elts eq length then
                  // the current elts form precisely one orbit
                  break;
                else
                  Exclude(~elts, e1);
                  orbit := normalize({H| u*e1 : u in us});
                  // assert orbit subset elts;
                  elts diff:= orbit;
                end if;
              end while;
            end if;
          end for; // ie

          if debug and small_prime then // this checks the two methods against eachother
            bool, tpsji := IsDefined(tps, <j,i>); assert bool;
            assert #ts eq #tpsji;
            for t in ts do 
              assert #[tt : tt in tpsji | tt/t in  LeftOrder(ridls[i])] eq 1; 
            end for;
            for t in tpsji do 
              assert #[tt : tt in ts | tt/t in  LeftOrder(ridls[i])] eq 1; 
            end for;
          end if;

          tps[<j,i>] := ts;
        end for; // i
      end for; // j

    end if; // small_prime
    IndentPop();

    // Sanity checks
    // (we really need the first check, it actually once failed for a huge prime p)
    keys := Keys(tps);
    for j in rows do
      assert &+ [#tps[<j,i>] : i in [1..h] | <j,i> in keys] eq num; 
    end for; 
    if debug then
      if rows eq [1..h] then
        tps0 := OH`RightIdealClasses[record_idx]`tps;
        tps_rows0 := OH`RightIdealClasses[record_idx]`tps_rows;
        TP := Matrix(h, [Integers()| IsDefined(tps,<j,i>) select #tps[<j,i>] else 0 : i,j in [1..h]]);
        for P0 in Keys(tps0) do
          if tps_rows0[P0] eq [1..h] then
            TP0 := Matrix(h, [Integers()| IsDefined(tps0[P0],<j,i>) select #tps0[P0][<j,i>] else 0 : i,j in [1..h]]);
            assert TP*TP0 eq TP0*TP;
          end if;
        end for; 
      end if;
    end if;

    OH`RightIdealClasses[record_idx]`tps[P] := tps;
    bool, old_rows := IsDefined(OH`RightIdealClasses[record_idx]`tps_rows, P);
    OH`RightIdealClasses[record_idx]`tps_rows[P] := bool select Sort(old_rows cat rows) else rows;

    // (previously) loop over several Ps ended here
    
  IndentPop();
  vprint ModFrmHil: "Precomputation time:", Cputime(time0);
end procedure;
