import "copypaste/definite.m" : HilbertModularSpaceDirectFactors, WeightRepresentation;
import "copypaste/hackobj.m" : IsBianchi, TopAmbient;
import "copypaste/precompute.m" : get_rids;
import "hackobj.m" : HMF0;
import "hecke.m" : checks, operator, hecke_matrix_field;

/**************** New Attributes **********************/
declare attributes ModFrmHil : Diamond;

/**************** New intrinsics **********************/

intrinsic '*'(a::RngOrdIdl, I::AlgAssVOrdIdl) -> AlgAssVOrdIdl
{Given an ideal a of R, and an ideal I of O, an order over R, Returns the ideal a*I.}
  return &+[g * I : g in Generators(a)];
end intrinsic;

// an intrinsic to get the weight base field of a magma space

intrinsic WeightBaseField(M::ModFrmHil) -> Fld
{Returns the base field of the weight representation.}
    if not assigned M`weight_base_field then
	if Seqset(Weight(M)) eq {2} then
	    return Rationals();
	end if;
	if assigned M`basis_matrix_wrt_ambient then
	    return BaseRing(M`basis_matrix_wrt_ambient);
	end if;
	if assigned M`Ambient and assigned M`Ambient`weight_base_field then
	    return M`Ambient`weight_base_field;
	end if;
	// No choice, we have to compute the weight representation for M
	_ := WeightRepresentation(M);
	if assigned M`basis_matrix_wrt_ambient then
	    return BaseRing(M`basis_matrix_wrt_ambient);
	end if;
	if assigned M`Ambient and assigned M`Ambient`weight_base_field then
	    return M`Ambient`weight_base_field;
	end if;
    end if;
    assert assigned M`weight_base_field;
    return M`weight_base_field;
end intrinsic;

/********************************************************/

// get the Eichler order corresponding to the level N in the order LO
function getEichlerOrder(M, LO, N)
    R := BaseRing(LO);
    basis_LO := Generators(LO);
    sm := M`splitting_map;
    sm_mats := Transpose(Matrix([Eltseq(sm(x)) : x in basis_LO]));
    rels := Matrix([sm_mats[3]]); // we want upper triangular matrices under sm
    rels := ChangeRing(rels, quo<R | N>);
    ker := Kernel(Transpose(rels));
    ker_basis := [ChangeRing(v, R) : v in Basis(ker)];
    a_invs := [&+[v[i]*basis_LO[i] : i in [1..#basis_LO]]
	       : v in ker_basis];
    NLO := [g*x : g in Generators(N), x in basis_LO];
    O := Order(a_invs cat NLO);
    // making sure we obtain a suborder of the right discriminant
    assert Discriminant(O) eq N;
    assert &and[x in LO : x in Generators(O)];
    return O;
end function;

// get the right ideal IJ_a of O, corresponding to the P1 representative a
function getEichlerOrderIdeal(M, I, a, O, N)
    R := BaseRing(LeftOrder(I));
    basis_I := Generators(I);
    sm := M`splitting_map;
    sm_mats := Transpose(Matrix([Eltseq(sm(x)) : x in basis_I]));
    // These are matrices that map to a in P1
    rels := Matrix([a[2,1]*sm_mats[1]-a[1,1]*sm_mats[3]]);
    rels := ChangeRing(rels, quo<R | N>);
    ker := Kernel(Transpose(rels));
    ker_basis := [ChangeRing(v, R) : v in Basis(ker)];
    a_invs := [&+[v[i]*basis_I[i] : i in [1..#basis_I]]
	       : v in ker_basis];
    NI := [g*x : g in Generators(N), x in basis_I];
    IJ := rideal< O | a_invs cat NI>;
    return IJ;
end function;

function DiamondOperatorDefiniteBig(M, J)
    assert IsDefinite(M);
    
    // Form here on we assume this is an ambient space
    assert (not assigned M`Ambient);
    
    N := Level(M);
    weight2 := Seqset(Weight(M)) eq {2};
    easy := weight2 and N eq Discriminant(QuaternionOrder(M));
    // easy = basis of big space is given by the rids
  
    // !! TODO : This is now redundant, unless the weight is 2
    // Once we get it to work, fix that
    F_weight := WeightBaseField(M);
    ideal_classes := get_rids(M);
    h := #ideal_classes;
    
    // J acts by left multiplication on the classes of right ideals.
    JIs := [J*I : I in ideal_classes];
    // This creates a permutation of the ideal classes, which we now construct
    perm := &cat[[j : j in [1..h] | IsIsomorphic(JI, ideal_classes[j])] : JI in JIs];
    
    // TODO - there are more cases to distinguish here.
    // I am not completely sure when and if the direct factors are actually called
    // However, if they are not needed for computing the Hecke operator above,
    // the basis matrix describes the embedding of M into the space of modular forms.
    
    // This is an artifact of the implementation -
    // When the weight is trivial, the basis_matrix describes the cuspidal space inside
    // the entire space of modular forms. We have to dig it out.
    // In the general case, the matrix describes the embedding into the h copies of W.
    // This makes sense since the entire space is cuspidal, but requires different handling.
    
    // if not assigned M`ModFrmHilDirFacts then
    if easy then 
	d_J := PermutationMatrix(F_weight,perm);
	return d_J;
    end if;
    HMDF := HilbertModularSpaceDirectFactors(M);
    sm := M`splitting_map;
    nCFD := [#hmdf`CFD : hmdf in HMDF];
    p1reps := [hmdf`PLD`P1Rep : hmdf in HMDF];
    lookups := [hmdf`PLD`Lookuptable : hmdf in HMDF];
    fds := [hmdf`PLD`FD : hmdf in HMDF];
    I := M`rids;
    rids := [ ];
    // we get the Eichler order
    O := getEichlerOrder(M, QuaternionOrder(M), Level(M));
    for rid_idx in [1..#HMDF] do
	Ii := I[rid_idx];
	N := HMDF[rid_idx]`PLD`Level;
	for a in fds[rid_idx] do
	    IJa := getEichlerOrderIdeal(M, Ii, a, O, N);
	    Append(~rids, IJa);
	end for;
    end for;
    h := #rids;
    wd := M`weight_dimension;
    zero := MatrixAlgebra(F_weight, wd)!0;
    blocks := [[zero : j in [1..h]] : i in [1..h]];
    weight2 := Seqset(Weight(M)) eq {2};
    for rid_idx in [1..h] do	
	assert exists(target_idx){i : i in [1..h]
				  | IsIsomorphic(rids[rid_idx], J*rids[i])};
	_, alpha := IsIsomorphic(rids[rid_idx],J*rids[target_idx]);
	assert J*rids[target_idx] eq alpha*rids[rid_idx];
	if weight2 then
	    alpha_rep := IdentityMatrix(F_weight, 1);
	else
	    alpha_rep := M`weight_rep(alpha);
	end if;
	blocks[target_idx][rid_idx] := alpha_rep;
    end for;
    dJ := BlockMatrix(blocks);
    d := Integers()!(Determinant(dJ));
    scale := &*([1] cat [pa[1]^(pa[2] div Nrows(dJ)) :
			 pa in Factorization(d)]);
//    assert scale eq Norm(J)^(CentralCharacter(M) div 2);
    dJ /:= scale;
    return dJ;
end function;

// At the moment we assume the action on the rids in trivial level is trivial.
// Later we will change that.
function getActionOnP1Reps(M, J, I_perm)
    sm := M`splitting_map;
    HMDF := M`ModFrmHilDirFacts;
    nCFD := [#hmdf`CFD : hmdf in HMDF];
    p1reps := [hmdf`PLD`P1Rep : hmdf in HMDF];
    lookups := [hmdf`PLD`Lookuptable : hmdf in HMDF];
    // O := getEichlerOrder(M);
    O := getEichlerOrder(M, QuaternionOrder(M), Level(M));
    // _, alpha := IsPrincipal(rideal<O | Generators(J)>);
    fds := [hmdf`PLD`FD : hmdf in HMDF];
    rid_perms := [];
    I := M`rids;
    alphas := [];
    units := [];
    for rid_idx in [1..#HMDF] do
	target_idx := I_perm[rid_idx];
	_, alpha := IsIsomorphic(I[target_idx], J*I[rid_idx]);
//	left_aI := lideal<LeftOrder(alpha*I[target_idx]) |
//			 Generators(alpha*I[target_idx])>;
//	left_JI := lideal<LeftOrder(J*I[rid_idx]) |
//			 Generators(J*I[rid_idx])>;
//	_, s := IsIsomorphic(left_JI, left_aI);
	rid_perm := [];
	OLIi := LeftOrder(I[rid_idx]);
	OLIj := LeftOrder(I[target_idx]);
	N := HMDF[target_idx]`PLD`Level;
	Oi := getEichlerOrder(M, OLIi, N);
	Oj := getEichlerOrder(M, OLIj, N);
	// for a in fds[target_idx] do
	for a in fds[rid_idx] do
	    //_, Ja := p1reps[target_idx](sm(alpha*s)*a, true, false);
	    //_, Ja := p1reps[target_idx](sm(s)*a, true, false);
	    _, Ja := p1reps[target_idx](sm(alpha)*a, true, false);
	    assert sm(alpha) eq HMDF[rid_idx]`PLD`splitting_map(alpha);
	    elt_data := lookups[target_idx][Ja];
	    Append(~rid_perm, Index(HMDF[target_idx]`CFD, elt_data[1]));
	    // For some reason this doesn't really work
	    // Append(~units, HMDF[target_idx]`max_order_units[elt_data[2]]);
	    // we proceed manually.
	    // IJa := getEichlerOrderIdeal(M, OLIi, a, Oi, N);
	    IJa := getEichlerOrderIdeal(M, I[rid_idx], a, O, N);
	    b := fds[target_idx][elt_data[1]];
	    // IJb := getEichlerOrderIdeal(M, OLIj, b, Oj, N);
	    IJb := getEichlerOrderIdeal(M, I[target_idx], b, O, N);
	    is_iso, true_alpha := IsIsomorphic(IJb, J*IJa);
	    assert is_iso;
	    u := true_alpha^(-1)*alpha;
	    Append(~units, u);
	end for;
	Append(~rid_perms, rid_perm);
        Append(~alphas, alpha);
    end for;
    cumdims := [&+nCFD[1..i] : i in [0..#nCFD]];
    big_perm := &cat[[cumdims[I_perm[i]] + idx : idx in rid_perms[i]] : i in [1..#rid_perms]];
    assert Set(big_perm) eq {1..&+nCFD};
    return big_perm, alphas, units;
end function;

// This function returns the matrix describing the action
// of the ideal J on the space M of Hilbert modular forms.
// These are the operators denoted by P(J) in [Voight]
// and by S(J) in [Shimura]

intrinsic DiamondOperator(M::ModFrmHil, J::RngOrdIdl) -> Mtrx
{Returns the matrix representing the diamond operator <J> on M.}

  bool, err, J := checks(M, J, "Diamond");
  require bool : err;
 
  return operator(M, J, "Diamond");
/*
    F_weight := getWeightBaseField(M);
    
    if Dimension(M) eq 0 then
	return MatrixAlgebra(F_weight, 0)!1;
    end if;

    // we compute it on the ambient space
    if assigned M`basis_matrix_wrt_ambient then 

	// (TO DO: is this always better than getting it directly from the big operator?)
	bm := M`basis_matrix_wrt_ambient;
	bmi := M`basis_matrix_wrt_ambient_inv;
	dJ_amb := DiamondOperator(M`Ambient, J);
	dJ_amb := ChangeRing(dJ_amb, BaseRing(bm));
	dJ := bm * dJ_amb * bmi;

	return dJ;
    end if;

    // so far we have implemented it only for the definite spaces
    assert IsDefinite(M);
    MA := TopAmbient(M);
    // This does not work at the moment
    // We replace with a slow version that actually works
    //dJ_big := DiamondOperatorDefiniteBig(MA, J);
    dJ_big := DiamondOperatorIdealsDefiniteBig(MA,J);
    return restriction(dJ_big, M);
*/
end intrinsic;

/*
function DiamondOperatorDefiniteBigOld(M, J)    

    assert IsDefinite(M);
    
    // Form here on we assume this is an ambient space
    assert (not assigned M`Ambient);
    
    N := Level(M);
    weight2 := Seqset(Weight(M)) eq {2};
    easy := weight2 and N eq Discriminant(QuaternionOrder(M));
    // easy = basis of big space is given by the rids

    // We would have liked to use that, but it is only available for parallel weight 2
    //raw_data := InternalHMFRawDataDefinite(M);
    //ideal_classes := raw_data`RightIdealClassReps;

    //    Instead, we force the computation of the attributes we care about.
    if (not assigned M`rids) then
	forceSpaceComputation(M);
    end if;
    F_weight := getWeightBaseField(M);
    ideal_classes := M`rids;
    h := #ideal_classes;
    
    // J acts by left multiplication on the classes of right ideals.
    JIs := [J*I : I in ideal_classes];
    // This creates a permutation of the ideal classes, which we now construct
    perm := &cat[[j : j in [1..h] | IsIsomorphic(JI, ideal_classes[j])] : JI in JIs];
    
    // TODO - there are more cases to distinguish here.
    // I am not completely sure when and if the direct factors are actually called
    // However, if they are not needed for computing the Hecke operator above,
    // the basis matrix describes the embedding of M into the space of modular forms.
    
    // This is an artifact of the implementation -
    // When the weight is trivial, the basis_matrix describes the cuspidal space inside
    // the entire space of modular forms. We have to dig it out.
    // In the general case, the matrix describes the embedding into the h copies of W.
    // This makes sense since the entire space is cuspidal, but requires different handling.
    
    // if not assigned M`ModFrmHilDirFacts then
    if easy then 
	d_J := PermutationMatrix(F_weight,perm);
	return d_J;
    end if;

    // not easy...
    // In order to gain the action on our space, we have to blockify according to the
    // subspaces of direct factors
    
    HMDF := M`ModFrmHilDirFacts;
    // dimensions of the different H0(W, Gamma_i)
    nCFD := [#xx`CFD : xx in HMDF];
    assert h eq #HMDF;
    wd := M`weight_dimension; // = 1 for weight2

    big_perm, alphas, units := getActionOnP1Reps(M, J, perm);
    hh := #big_perm;

    zero := MatrixAlgebra(F_weight, wd)!0;
    blocks := [[zero : j in [1..hh]] : i in [1..hh]];
    for rid_idx in [1..h] do
	target_idx := perm[rid_idx];
	alpha := alphas[target_idx];
	// alpha := alphas[target_idx];
	for i in [1..nCFD[rid_idx]] do
	    idx := &+nCFD[1..rid_idx-1] + i;
	    if weight2 then
		alpha_rep := IdentityMatrix(F_weight, 1);
	    else
		u := units[idx]^(-1);
		alpha_rep := M`weight_rep(alpha*u);
		
	    end if;
	    blocks[big_perm[idx]][idx] := alpha_rep;
	end for;
    end for;

    d_J := BlockMatrix(blocks);
    d := Integers()!(1/Determinant(d_J));
    scale := &*([1] cat [pa[1]^(pa[2] div Nrows(d_J)) : pa in Factorization(d)]);
    d_J *:= scale;
 
    big_perm := &cat[[wd*(big_perm[i]-1)+j : j in [1..wd]] : i in [1..#big_perm]];

    // This is the operator on the entire space of Hilbert modular forms
    if weight2 then
	assert d_J eq PermutationMatrix(F_weight, big_perm);
    end if;
    
    return d_J;
end function;
*/

// Here M is a ModFrmHil (HibertCuspForms(M))
// Currently just works for trivial weight.
function HeckeCharacterSubspace(M, chi)
    
    K := BaseRing(M);
    cl_K, cl_map := ClassGroup(K);
    if IsTrivial(cl_K) then
	return M;
    end if;
    Js := [cl_map(cl_K.i) : i in [1..Ngens(cl_K)]];
    dJs := [<J, DiamondOperator(M,J)> : J in Js];
    
    F_weight := WeightBaseField(M);
    Id_M := IdentityMatrix(F_weight, Dimension(M));
    
    subsp := &meet [Kernel(dJ[2] - chi(dJ[1])*Id_M) : dJ in dJs];

    dim := Dimension(subsp);
    
    Id_Msub := IdentityMatrix(F_weight, dim);
    
    M_sub := HMF0(BaseField(M), Level(M), 1*Integers(K), chi, Weight(M), CentralCharacter(M));
    M_sub`basis_matrix_wrt_ambient := BasisMatrix(subsp);
    
    M_sub`basis_matrix_wrt_ambient_inv := 
        Transpose(Solution( Transpose(M_sub`basis_matrix_wrt_ambient), Id_Msub));
    if assigned M`basis_matrix then
       M_sub`basis_matrix := M_sub`basis_matrix_wrt_ambient * M`basis_matrix;
       M_sub`basis_matrix_inv := Transpose(Solution( Transpose(M_sub`basis_matrix), Id_Msub));
    end if;

    M_sub`Ambient := M;
    M_sub`Dimension := dim;
    if assigned M`is_new then
      M_sub`is_new := M`is_new;
    end if;
    
    return M_sub;
end function;
