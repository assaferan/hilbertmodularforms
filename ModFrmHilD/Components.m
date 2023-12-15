///////////////////////////////////////////////////
//                                               //
//         Components of HMFs                    //
//                                               //
///////////////////////////////////////////////////

/* We implement components of HMFs as multivariate polynomials. In the
   background, we think of arithmetic operations as operations modulo an ideal
   (generated by elements q^\nu for \nu outside some "shadow box",
   cf. paper). In the code, we do not work with the ideal. Instead we use
   honest polynomial multiplications then discard unwanted coefficients.

   We provide two implementations: one that uses a multivariate (sparse)
   polynomial ring, and one that uses a tower of (dense) univariate polynomial
   rings. */

declare type ModFrmHilDEltComp;

declare attributes ModFrmHilDEltComp: CoefficientRing, // Rng
        Series, // RngMPolElt or RngUPolElt[...]
        ShadowSeries, //same
        Precision, // RngIntElt - the maximum norm of nn for which coefficients are stored
        Space, // ModFrmHilD - the HMF space that this ModFrmHilDEltComp is a component in
        ComponentIdeal; // RngOrdIdl

///////////////////////////////////////////////////
//                                               //
//         Access to attributes                  //
//                                               //
///////////////////////////////////////////////////

intrinsic GradedRing(f :: ModFrmHilDEltComp) -> ModFrmHilDGRng
{}
    return Parent(f`Space);
end intrinsic;

intrinsic SeriesRing(f :: ModFrmHilDEltComp) -> Rng
{}
    return Parent(Series(f));
end intrinsic;

intrinsic IsMultivariate(f :: ModFrmHilDEltComp) -> BoolElt
{}
    return Type(Series(f)) eq RngMPolElt;
end intrinsic;

intrinsic CoefficientRing(f :: ModFrmHilDEltComp) -> Rng
{}
    return f`CoefficientRing;
end intrinsic;

intrinsic Series(f :: ModFrmHilDEltComp) -> RngElt
{}
    if not assigned f`Series and assigned f`ShadowSeries then
        HMFGetSeriesFromShadow(f);
    end if;
    return f`Series;
end intrinsic;

intrinsic ShadowSeries(f :: ModFrmHilDEltComp) -> RngElt
{}
    if not assigned f`ShadowSeries and assigned f`Series then
        HMFGetShadowFromSeries(f);
    end if;
    return f`ShadowSeries;
end intrinsic;

intrinsic Precision(f :: ModFrmHilDEltComp) -> RngIntElt
{}
    return f`Precision;
end intrinsic;

intrinsic Space(f :: ModFrmHilDEltComp) -> ModFrmHilD
{}
    return f`Space;
end intrinsic;

intrinsic ComponentIdeal(f :: ModFrmHilDEltComp) -> RngOrdIdl
{}
    return f`ComponentIdeal;
end intrinsic;

intrinsic BaseField(f :: ModFrmHilDEltComp) -> FldNum
{}
    return BaseField(Space(f));
end intrinsic;

///////////////////////////////////////////////////
//                                               //
//         Access to coefficients                //
//                                               //
///////////////////////////////////////////////////

intrinsic Coefficient(f :: ModFrmHilDEltComp, nu :: FldNumElt
                      : InFunDomain := false) -> RngElt

{Returns the coefficient of nu in the Fourier series}

    M := GradedRing(f);
    bb := ComponentIdeal(f);
    n := Degree(BaseField(M));
    R := CoefficientRing(f);

    if not InFunDomain then
        nu, eps := FunDomainRep(M, bb, nu);
    end if;
    b, prec := IsDefined(M`FunDomainReps[bb], nu);

    require b: "Not in fundamental domain";
    require prec le Precision(M): "Not enough precision";

    a :=  HMFSeriesCoefficient(Series(f), M`FunDomainRepsOfPrec[bb][prec][nu]);
    if not InFunDomain then
        uc := UnitCharacters(Space(f))[bb];
        a := a * Evaluate(uc, eps);
    end if;

    return a;
end intrinsic;

// specify two functions of HMFSeriesCoefficient for multivariate and univariate.
// if we choose only one of these implementations, can remove duplicate
intrinsic HMFSeriesCoefficient(f :: RngUPolElt, exp :: SeqEnum[RngIntElt]) -> RngElt

{Internal function: get coefficient of f with the given exponent}

    n := #exp;
    g := f;
    for i in [0..(n-1)] do
        g := Coefficient(g, exp[n - i]);
    end for;
    return g;
end intrinsic;

intrinsic HMFSeriesCoefficient(f :: RngMPolElt, exp :: SeqEnum[RngIntElt]) -> RngElt

{Internal function: get coefficient of f with the given exponent}

    P := Parent(f);
    mon := Monomial(P, exp);
    return MonomialCoefficient(f, mon);
end intrinsic;

intrinsic Coefficients(f :: ModFrmHilDEltComp) -> Assoc

{Returns an associative array nu->a_nu for nu in the fundamental domain
up to Precision(f).}

    M := GradedRing(f);
    bb := ComponentIdeal(f);
    coeffs := AssociativeArray();
    precs := [p: p in M`PrecisionsByComponent[bb] | p le Precision(f)];
    for p in precs do
        for nu->exp in M`FunDomainRepsOfPrec[bb][p] do
            coeffs[nu] := HMFSeriesCoefficient(Series(f), exp);
        end for;
    end for;
    return coeffs;

end intrinsic;

///////////////////////////////////////////////////
//                                               //
//         Printing                              //
//                                               //
///////////////////////////////////////////////////

intrinsic Print(f :: ModFrmHilDEltComp, level :: MonStgElt : num_coeffs := 10)
{}
    if level in ["Default", "Minimal", "Maximal"] then
        prec := Precision(f);
        bb := ComponentIdeal(f);
        M := GradedRing(f);
        precs := [p: p in M`PrecisionsByComponent[bb] | p le prec];
        printf "Hilbert modular form component for ideal class bb = %o at precision %o\n",
               bb, prec;
        printf "Coefficients \n\t(norm, nu)  |--->   a_nu:";
        count := 0;
        for p in precs do
            for nu->exp in M`FunDomainRepsOfPrec[bb][p] do
                printf "\n\t(%o, %o)  |--->   %o", p, nu,
                       HMFSeriesCoefficient(Series(f), exp);
                count +:= 1;
            end for;
            if count ge num_coeffs then
                printf "\n...";
                break;
            end if;
        end for;
        printf "\n\n";

    elif level eq "Magma" then
        error "not implemented yet!";
    else
        error "not a valid printing level.";
    end if;
end intrinsic;

///////////////////////////////////////////////////
//                                               //
//         Pruning the series                    //
//                                               //
///////////////////////////////////////////////////

intrinsic HMFSeriesSubset(f :: RngMPolElt, exps :: SeqEnum) -> RngMPolElt

{Internal function: extract only the specified exponents from the series}

    R := Parent(f);
    mons := [Monomial(R, e): e in exps];
    coeffs := [MonomialCoefficient(f, mon): mon in mons];
    return Polynomial(coeffs, mons);
end intrinsic;

intrinsic HMFSeriesSubset(f :: RngUPolElt, exps :: SeqEnum) -> RngUPolElt

{Internal function: extract only the specified exponents from the series}

    if #exps eq 0 then
        return Parent(f) ! 0;
    end if;

    n := #exps[1];
    P := Parent(f);
    last_entries := [e[n]: e in exps];
    new_coeffs := [0: i in [0..Max(last_entries)]];

    if n eq 1 then
        for e in exps do
            new_coeffs[e[1]] := Coefficient(f, e[1]);
        end for;
    else
        last_entries := SetToSequence(SequenceToSet(last_entries));
        for d in last_entries do
            rec_exps := [e[1..(n-1)]: e in exps | e[n] eq d];
            new_coeffs[d] := HMFSeriesSubset(Coefficient(f, d), rec_exps);
        end for;
    end if;

    return P ! new_coeffs;
end intrinsic;

intrinsic HMFPruneSeries(M :: ModFrmHilDGRng, bb :: RngOrdIdl, f :: RngElt :
                         Precision := Precision(M)
    ) -> RngElt

{Internal function: returns a pruned version of the series f}

    exps := [];
    precs := [p: p in M`PrecisionsByComponent[bb] | p le Precision];
    for p in precs do
        for nu->e in M`FunDomainRepsOfPrec[bb][p] do
            Append(~exps, e);
        end for;
    end for;
    return HMFSeriesSubset(f, exps);

end intrinsic;

intrinsic HMFPruneSeries(f :: ModFrmHilDEltComp : Precision := Precision(f))

{Internal function: replace f`Series by pruned version}

    f`Series := HMFPruneSeries(GradedRing(f), ComponentIdeal(f), Series(f) :
                               Precision := Precision(f));
end intrinsic;

intrinsic HMFPruneShadowSeries(M :: ModFrmHilDGRng, bb :: RngOrdIdl, f :: RngElt :
                               Precision := Precision(M)
    ) -> RngElt

{Internal function: returns a pruned version of the shadow series f}

    exps := [];
    precs := [p: p in M`PrecisionsByComponent[bb] | p le Precision];
    for p in precs do
        for nu->exp_nu in M`FunDomainRepsOfPrec[bb][p] do
            for eps->e in M`Shadows[bb][nu] do
                Append(~exps, e);
            end for;
        end for;
    end for;
    return HMFSeriesSubset(f, exps);

end intrinsic;

intrinsic HMFPruneShadowSeries(f :: ModFrmHilDEltComp : Precision := Precision(f))

{Internal function: replace f`ShadowSeries by pruned version}

    f`ShadowSeries := HMFPruneShadowSeries(GradedRing(f), ComponentIdeal(f), ShadowSeries(f) :
                                           Precision := Precision(f));
end intrinsic;

///////////////////////////////////////////////////
//                                               //
//         Series to shadow and back             //
//                                               //
///////////////////////////////////////////////////

intrinsic HMFGetSeriesFromShadow(f :: ModFrmHilDEltComp)

{Internal function: compute f`Series from f`ShadowSeries}

    f`Series := HMFPruneSeries(GradedRing(f), ComponentIdeal(f), f`ShadowSeries :
                               Precision := Precision(f));
end intrinsic;

intrinsic HMFGetShadowFromSeries(f :: ModFrmHilDEltComp)

{Internal function: compute f`ShadowSeries from f`Series}

    M := GradedRing(f);
    bb := ComponentIdeal(f);
    uc := UnitCharacters(Space(f))[bb];

    exps := [];
    coeffs := [];
    precs := [p : p in M`PrecisionsByComponent[bb] | p le Precision(f)];
    for prec in precs do
        for nuprime->exp_nuprime in M`FunDomainRepsOfPrec[bb][prec] do
            a := HMFSeriesCoefficient(f`Series, exp_nuprime);
            for eps->exp_nu in M`Shadows[bb][nuprime] do
                Append(~coeffs, a * Evaluate(uc, eps));
                Append(~exps, exp_nu);
            end for;
        end for;
    end for;

    f`ShadowSeries := HMFConstructSeries(SeriesRing(f), exps, coeffs);
end intrinsic;

intrinsic HMFConstructSeries(R :: RngMPol, exps :: SeqEnum, coeffs :: SeqEnum[RngElt]
    ) -> RngMPolElt

{Internal function: construct the Fourier expansion with the specified
coefficients as an element of R}

    mons := [Monomial(R, e): e in exps];
    return Polynomial(coeffs, mons);
end intrinsic;

intrinsic HMFConstructSeries(R :: RngUPol, exps :: SeqEnum, coeffs :: SeqEnum[RngElt]
    ) -> RngUPolElt

{Internal function: construct the Fourier expansion with the specified
coefficients as an element of R}

    if #exps eq 0 then
        return R!0;
    end if;

    n := #exps[1];
    last_entries := [e[n]: e in exps];
    pol_coeffs := [0: i in [0..Max(last_entries)]];
    if n eq 1 then
        for i in [1..#exps] do
            pol_coeffs[exps[i][1]] := coeffs[i];
        end for;
    else
        last_entries := SetToSequence(SequenceToSet(last_entries));
        for d in last_entries do
            rec_exps := [];
            rec_coeffs := [];
            for i in [1..#exps] do
                e := exps[i];
                if e[n] eq d then
                    Append(~rec_exps, e[1..(n-1)]);
                    Append(~rec_coeffs, coeffs[i]);
                end if;
            end for;
            pol_coeffs[d] := HMFConstructSeries(BaseRing(R), rec_exps, rec_coeffs);
        end for;
    end if;

    return R ! pol_coeffs;
end intrinsic;



///////////////////////////////////////////////////
//                                               //
//         ModFrmHilDEltComp constructors        //
//                                               //
///////////////////////////////////////////////////

intrinsic HMFSeriesRing(R :: Rng, n :: RngIntElt : Multivariate := true) -> Rng

{Internal function: returns the series ring used in HMF components}

    if Multivariate then
        S := PolynomialRing(R, n);
    else
        S := R;
        for i in [1..n] do
            S := PolynomialRing(S);
        end for;
    end if;

    return S;
end intrinsic;

intrinsic HMFComponent(Mk :: ModFrmHilD, bb :: RngOrdIdl, f :: RngElt, prec :: RngIntElt :
                       Shadow := false, Prune := true
    ) -> ModFrmHilDEltComp

{Internal function: constructs the HMF component whose Fourier series is
specified by the polynomial f at the given precision. Parent(f) should either
be a multivariate polynomial ring or a tower of univariate polynomial rings.}

    n := Degree(BaseField(Mk));

    if Type(f) eq RngMPolElt then
        R := BaseRing(Parent(f));
    elif Type(f) eq RngUPolElt then
        R := Parent(f);
        for i in [1..n] do
            R := BaseRing(Parent(R));
        end for;
    else
        error "Unsupported type for Fourier expansions: ", Type(f);
    end if;

    g := New(ModFrmHilDEltComp);
    g`Space := Mk;
    g`ComponentIdeal := bb;
    g`CoefficientRing := R;
    g`Precision := prec;
    if Shadow then
        g`ShadowSeries := f;
    else
        g`Series := f;
    end if;

    if Prune then
        if Shadow then
            HMFPruneShadowSeries(g);
        else
            HMFPruneSeries(g);
        end if;
    end if;
    return g;

end intrinsic;

intrinsic HMFComponent(Mk :: ModFrmHilD, bb :: RngOrdIdl, coeff_array :: Assoc
                       : Multivariate := true, CoefficientRing := DefaultCoefficientRing(Mk),
                         Precision := Precision(Parent(Mk))
    ) -> ModFrmHilDEltComp

{Constructs the HMF component to precision prec whose Fourier coefficients are
specified by the given array indexed by nus in the fundamental domain.

By default, we assume that the coefficient ring is the default coefficient ring
of Mk, and that coefficients are specified up to the default precision of the
ambient graded ring. The user may specify another coefficient ring or a lower
precision instead.}

    M := Parent(Mk);
    n := Degree(BaseField(Mk));

    // Gather exponents and coefficients
    precs := [p: p in M`PrecisionsByComponent[bb] | p le Precision];
    exps := [];
    coeffs := [];
    for p in precs do
        for nu->exp in M`FunDomainRepsOfPrec[bb][p] do
            b, coeff := IsDefined(coeff_array, nu);
            require b: "Coefficient not found for index: ", nu;
            Append(~exps, exp);
            Append(~coeffs, coeff);
        end for;
    end for;

    R := HMFSeriesRing(CoefficientRing, n : Multivariate := Multivariate);
    f := HMFConstructSeries(R, exps, coeffs);
    return HMFComponent(Mk, bb, f, Precision: Shadow := false, Prune := false);

end intrinsic;

intrinsic HMFComponentZero(Mk :: ModFrmHilD, bb :: RngOrdIdl
                                : Multivariate := true
    ) -> ModFrmHilDEltComp

{Returns the HMF component that is identically zero on the bb component.}

    n := Degree(BaseField(Mk));
    R := DefaultCoefficientRing(Mk);
    S := HMFSeriesRing(R, n : Multivariate := Multivariate);
    return HMFComponent(Mk, bb, S ! 0, Precision(Parent(Mk)) : Shadow := true, Prune := false);
end intrinsic;

intrinsic HMFComponentOne(Mk :: ModFrmHilD, bb :: RngOrdIdl
                          : Multivariate := true
    ) -> ModFrmHilDEltComp

{Returns the HMF component that is identically one on the bb component.}

    n := Degree(BaseField(Mk));
    R := DefaultCoefficientRing(Mk);
    S := HMFSeriesRing(R, n : Multivariate := Multivariate);
    return HMFComponent(Mk, bb, S ! 1, Precision(Parent(Mk)) : Shadow := true, Prune := false);
end intrinsic;

///////////////////////////////////////////////////
//                                               //
//         Arithmetic operations                 //
//                                               //
///////////////////////////////////////////////////

intrinsic ChangeRing(f :: ModFrmHilDEltComp, R :: Rng) -> ModFrmHilDEltComp

{Constructs the HMF component that is identical to f, except that its
coefficient ring is extended to R.}

    Mk := Space(f);
    n := Degree(BaseField(Mk));
    bb := ComponentIdeal(f);
    ser := ShadowSeries(f);
    prec := Precision(f);
    S := HMFSeriesRing(R, n : Multivariate := IsMultivariate(f));

    return HMFComponent(Mk, bb, S ! ser, prec : Shadow := true, Prune := false);
end intrinsic;

intrinsic IsZero(f :: ModFrmHilDEltComp) -> BoolElt
{}
    return IsZero(Series(f));
end intrinsic;

intrinsic 'eq'(f :: ModFrmHilDEltComp, g :: ModFrmHilDEltComp) -> BoolElt
{}
    return Space(f) eq Space(g)
           and ComponentIdeal(f) eq ComponentIdeal(g)
           and CoefficientRing(f) eq CoefficientRing(g)
           and Precision(f) eq Precision(g)
           and Series(f) eq Series(g);
end intrinsic;

intrinsic '+'(f :: ModFrmHilDEltComp, g :: ModFrmHilDEltComp) -> ModFrmHilDEltComp
{}
    require Space(f) eq Space(g) : "Cannot add HMF components from different spaces";
    require ComponentIdeal(f) eq ComponentIdeal(g): "Cannot add HMF components attached to different narrow class group representatives";

    bb := ComponentIdeal(f);
    prec := Min(Precision(f), Precision(g));
    prune := not (Precision(f) eq Precision(g));
    return HMFComponent(Space(f), ComponentIdeal(f), Series(f) + Series(g), prec
                        : Shadow := false, Prune := prune);
end intrinsic;

intrinsic '*'(c :: RngElt, f :: ModFrmHilDEltComp) -> ModFrmHilDEltComp
{}
    R := CoefficientRing(f);
    b, c_K := IsCoercible(R, c);
    if not b then
        b, c_K := IsStrongCoercible(R, c);
    end if;
    require b : "Cannot scale an HMF by a scalar not coercible into its coefficient field";

    return HMFComponent(Space(f), ComponentIdeal(f), c_K * Series(f), Precision(f)
                        : Shadow := false, Prune := false);
end intrinsic;

intrinsic '-'(f :: ModFrmHilDEltComp, g :: ModFrmHilDEltComp) -> ModFrmHilDEltComp
{}
    R := CoefficientRing(f);
    return f + R!(-1) * g;
end intrinsic;

intrinsic '*'(f :: ModFrmHilDEltComp, g :: ModFrmHilDEltComp) -> ModFrmHilDEltComp
{}
    bb := ComponentIdeal(f);
    Rf := CoefficientRing(f);
    Rg := CoefficientRing(g);
    serf := ShadowSeries(f);
    serg := ShadowSeries(g);
    require bb eq ComponentIdeal(g): "Cannot multiply HMF components on different components";

    if not Rf eq Rg then // coerce automatically
        n := Degree(BaseField(f));
        multivariate := (Type(serf) eq RngMPolElt);
        Rf := Compositum(Rf, Rg);
        S := HMFSeriesRing(Rf, n : Multivariate := multivariate);
        serf := S ! serf;
        serg := S ! serg;
    end if;

    prec := Min(Precision(f), Precision(g));
    if Precision(f) gt prec then
        serf := HMFPruneShadowSeries(serf : Precision := prec);
    elif Precision(g) gt prec then
        serg := HMFPruneShadowSeries(serg : Precision := prec);
    end if;

    return HMFComponent(Space(f) * Space(g), bb, serf * serg, prec :
                        Shadow := true, Prune := true);
end intrinsic;

intrinsic '^'(f :: ModFrmHilDEltComp, n :: RngIntElt) -> ModFrmHilDEltComp
{}
    require n ge 0: "Cannot compute inverse of HMF component";
    serf := ShadowSeries(f);
    prec := Precision(f);
    g := serf;
    bits := Reverse(Intseq(n));
    bits := bits[1..(#bits - 1)];
    for i in bits do
        g := g^2;
        g := HMFPruneShadowSeries(g : Precision := prec);
        if i eq 1 then
            g := g * f;
            g := HMFPruneShadowSeries(g : Precision := prec);
        end if;
    end for;

    return HMFComponent(Space(f)^n, ComponentIdeal(f), g, prec :
                        Shadow := true, Prune := false);
end intrinsic;

intrinsic '/'(f :: ModFrmHilDEltComp, g :: ModFrmHilDEltComp) -> ModFrmHilDEltComp
{}
    n := Degree(BaseField(g));
    a0 := HMFSeriesCoefficient(Series(g), [0: i in [1..n]]);
    bb := ComponentIdeal(f);
    require IsInvertible(a0) : "Cannot divide if the constant coefficient is not invertible";
    require bb eq ComponentIdeal(g) : "Cannot divide HMF components on different components";

    // Coerce automatically
    Rf := CoefficientRing(f);
    Rg := CoefficientRing(g);
    if not Rf eq Rg then
        n := Degree(BaseField(f));
        Rf := Compositum(Rf, Rg);
        f := ChangeRing(f, Rf);
        g := ChangeRing(g, Rg);
    end if;

    // Reduce to g = 1 + ...
    a0inv := (Rf ! a0)^(-1);
    f := a0inv * f;
    g := a0inv * g;
    serf := ShadowSeries(f);
    serg := ShadowSeries(g);

    // Get shadow series at minimum precision
    prec := Min(Precision(f), Precision(g));
    if prec lt Precision(f) then
        serf := HMFPruneShadowSeries(serf : Precision := prec);
    elif prec lt Precision(g) then
        serg := HMFPruneShadowSeries(serg : Precision := prec);
    end if;

    // Invert
    u := 1 - serg;
    inv := SeriesRing(g) ! 1;
    u := HMFPruneShadowSeries(u : Precision := prec);
    inv := 1 + u;
    while u ne 0 do
        inv := (1 + u) * inv;
        inv := HMFPruneShadowSeries(inv : Precision := prec);
        u := u * u;
        u := HMFPruneShadowSeries(u : Precision := prec);
    end while;
    inv := serf * inv;
    inv := HMFPruneShadowSeries(inv : Precision := prec);

    return HMFComponent(Space(f) / Space(g), bb, inv, prec :
                        Shadow := true, Prune := false);
end intrinsic;

///////////////////////////////////////////////////
//                                               //
//         Advanced operations                   //
//                                               //
///////////////////////////////////////////////////

intrinsic Trace(f :: ModFrmHilDEltComp) -> ModFrmHilDEltComp

{Returns the trace of f down to the default coefficient field of Space(f),
assuming that its coefficient ring is a number field.}

    R := CoefficientRing(f);
    K := DefaultCoefficientRing(Space(f));
    tracemap := map< R->K | x:->Trace(x, K) >;
    return MapCoefficients(tracemap, f);
end intrinsic;

intrinsic MapCoefficients(m :: Map, f :: ModFrmHilDEltComp) -> ModFrmHilDEltComp

{Returns the HMF component obtained by applying the map m to all coefficients of f}

    M := GradedRing(f);
    bb := ComponentIdeal(f);
    n := Degree(BaseField(f));
    new_ring := Codomain(m);
    new_series_ring := HMFSeriesRing(new_ring, n : Multivariate := IsMultivariate(f));

    precs := [p: p in M`PrecisionsByComponent[bb] | p le Precision(f)];
    exps := [];
    coeffs := [];
    for p in precs do
        for nu->e in M`FunDomainRepsOfPrec[bb][p] do
            Append(~exps, e);
            Append(~coeffs, m(HMFSeriesCoefficient(Series(f), e)));
        end for;
    end for;
    new_series := HMFConstructSeries(new_series_ring, exps, coeffs);
    return HMFComponent(Space(f), ComponentIdeal(f), new_series, Precision(f):
                        Shadow := false, Prune := false);
end intrinsic;

intrinsic Inclusion(f :: ModFrmHilDEltComp, Mk :: ModFrmHilD, mm :: RngOrdIdl
    ) -> ModFrmHilDEltComp

{Takes a form f(z) and produces f(mm*z) in Mk (of level NN) with component
ideal class [mm*bb].}

    Mk_f := Space(f);
    M_f := Parent(Mk_f);
    M := Parent(Mk);
    N1 := Level(Mk_f);
    N2 := Level(Mk);
    chi := Character(Mk);
    chif := Character(Mk_f);
    mf, pf := Modulus(chif);
    ZF := Integers(M);
    coeff_ring := CoefficientRing(f);

    require Weight(Mk_f) eq Weight(Mk): "Weight(f) is not equal to Weight(Mk)";
    require chif eq Restrict(chi, mf, pf): "Character(f) is not equal to Character(Mk)";
    require UnitCharacters(Mk_f) eq UnitCharacters(Mk): "UnitCharacters(f) is not equal to UnitCharacters(Mk)";
    require N2 subset N1: "Level of f does not divide level of Mk";
    require N2 subset mm: "Ideal mm does not divide level of Mk";

    bb := ComponentIdeal(f);
    mmbb := NarrowClassRepresentative(M, mm * bb);
    prec := Min(Norm(mm) * Precision(f), Precision(M));

    coeffs := AssociativeArray();
    mminv := mm^-1;
    mmbbpinv := (M`NarrowClassGroupRepsToIdealDual[mmbb])^(-1);
    for nn -> nu in IdealToRep(M)[mmbb] do
        if Norm(nu) * Norm(mmbbpinv) le prec and IsIntegral(nn * mminv) then
            coeffs[nu] := Coefficient(f, IdealToRep(M)[bb][ZF!!(nn*mminv)]
                                     : InFunDomain := true);
        else
            coeffs[nu] := coeff_ring ! 0;
        end if;
    end for;
    return HMFComponent(Mk, mmbb, coeffs:
                        Multivariate := IsMultivariate(f), CoefficientRing := coeff_ring,
                        Precision := prec);
end intrinsic;
