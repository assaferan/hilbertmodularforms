function R1(D,N)
    return [p : p in PrimeDivisors(D) | N mod p ne 0 ];
end function;

function R2(D,N)
    return [p : p in PrimeDivisors(D) | Valuation(N,p) ge 2*Valuation(D,p) ];
end function;

intrinsic PrimeDiscriminant(D::RngIntElt,q::RngIntElt) -> RngIntElt
{Return the prime discriminant D(q).}
    require D mod q eq 0 : "q must divide D.";
    require IsFundamentalDiscriminant(D) : "D must be a fundamental discriminant.";
    require IsPrime(q) : "q must be a prime.";
    sign := (q mod 4 eq 1) select 1 else -1;
    if (q eq 2) then
	sign := (-1)^(#[p : p in PrimeDivisors(D) | p mod 4 eq 3]);
    end if;
    return sign*q^Valuation(D,q);
end intrinsic;

function IsHZEmpty(Gamma,N)
    D := Discriminant(BaseField(Gamma));
    b := Component(Gamma);
    R1_primes := R1(D,N);
    for q in R1_primes do
	Dq := PrimeDiscriminant(D,q);
	chi := KroneckerCharacter(Dq);
	hilb := HilbertSymbol(Norm(b), D, q);
	if (chi(N) ne hilb) then
	    return true;
	end if;
    end for;
    return false;
end function;

// For some reason, these are not supported in Magma

// This could be made more efficient. For now using a simple implementation.
intrinsic IsPrimePower(I::RngOrdIdl) -> BoolElt
{True if I is a power of a prime ideal.}
  return #Factorization(I) eq 1;
end intrinsic;

intrinsic Sqrt(x::RngOrdResElt) -> RngOrdResElt
{The square root of x.}
  ZF_mod_N := Parent(x);
  N := Modulus(ZF_mod_N);	 
  require IsPrimePower(N) : "At the moment only supports prime powers";
  ZF := Order(N);
  frakp := Factorization(N)[1][1];
  ZFp, comp_p := Completion(ZF, frakp);
  pi := UniformizingElement(ZFp);
  // This is to handle the p = 2 case
  sqr := comp_p(ZF!x);
  if IsSquare(sqr) then
      sqrt_xp := Sqrt(sqr);
  else
      val_N := Valuation(N, frakp);
      sqr +:= pi^val_N;
      if IsSquare(sqr) then
	  sqrt_xp := Sqrt(sqr);
      else
	  // This is the case p = 2.
	  // Here I just give up and brute force my way for now
	  assert exists(sqrt_x){y : y in ZF_mod_N | y^2 eq x};
	  return sqrt_x;
	  /*
	  v := Valuation(sqr);
	  assert (v gt 0) and IsEven(v);
	  sqr div:= pi^v;
	  ZF_mod_NN, red_NN := quo<ZF | frakp^(val_N - v)>;
	  t := Sqrt(ZF_mod_NN!(((quo<ZFp | pi^(val_N - v)>)!sqr)@@comp_p));
	  sqrt_xp := pi^(v div 2)*comp_p(ZF!t);
	  */
      end if;
  end if;
  sqrt_x := Parent(x)!((sqrt_xp + O(pi^Valuation(N,frakp)))@@comp_p);
  assert sqrt_x^2 eq x;
  return sqrt_x;
end intrinsic;

intrinsic GetPossibleThetas(Gamma::GrpHilbert, N::RngIntElt) -> SeqEnum[Assoc]
{Get the possible values of the invariants theta = theta_p for p in R1 for the HZ divisor F_N.}
    require not IsHZEmpty(Gamma,N) : "The image of F_N in X_Gamma is empty!";
    D := Discriminant(Integers(BaseField(Gamma)));
    b := Component(Gamma);
    ZF := Order(b);
    F := NumberField(ZF);
    R1_primes := R1(D,N);
    all_thetas := AssociativeArray(R1_primes);
    if IsEmpty(R1_primes) then return [all_thetas]; end if;
    for p in R1_primes do
	v := Valuation(D,p);
	frakp := PrimeIdealsOverPrime(F,p)[1];
	ZFmodpv, red := quo<ZF | frakp^Valuation(D,p)>;
	if (p eq 2) and (v eq 2) then
	    d := SquareFree(D);
	    thetas := [1@@red, Sqrt(ZF!d)];
	else
	    x := Sqrt(ZFmodpv!Norm(b)*N)@@red;
	    thetas := [x, -x];
	end if;
	all_thetas[p] := thetas;
    end for;
    thetas := [];
    for theta in CartesianProduct([all_thetas[p] : p in R1_primes]) do
	theta_assoc := AssociativeArray(R1_primes);
	for i->p in R1_primes do
	    theta_assoc[p] := theta[i];
	end for;
	Append(~thetas,theta_assoc);
    end for;
    return thetas;
end intrinsic;

intrinsic GetPossibleEtas(Gamma::GrpHilbert, N::RngIntElt) -> SeqEnum[Assoc]
{Get the possible values of the invariants eta = eta_p for p in R2 for the HZ divisor F_N.}
    require not IsHZEmpty(Gamma,N) : "The image of F_N in X_Gamma is empty!";
    D := Discriminant(Integers(BaseField(Gamma)));
    R2_primes := R2(D,N);
    all_etas := AssociativeArray(R2_primes);
    if IsEmpty(R2_primes) then return [all_etas]; end if;
    F := BaseField(Gamma);
    ZF := Integers(F);
    for p in R2_primes do
	// frakp := PrimeIdealsOverPrime(F,p)[1];
	if (p eq 2) then
	    // ZF_mod_pv, red := quo<ZF | frakp^Valuation(D,2)>
	    // all_etas[p] := [ZF | 1, 3];
	    all_etas[p] := [Integers() | 1, 3];
	else
	    // ZF_mod_pv, red := ResidueClassField(frakp);
	    // all_etas[p] := [ZF| 1, Nonsquare(GF(p))@@red];
	    all_etas[p] := [Integers() | 1, Integers(p)!Nonsquare(GF(p))];
	end if;
    end for;
    etas := [];
    for eta in CartesianProduct([all_etas[p] : p in R2_primes]) do
	eta_assoc := AssociativeArray(R2_primes);
	for i->p in R2_primes do
	    eta_assoc[p] := eta[i];
	end for;
	Append(~etas,eta_assoc);
    end for;
    return etas;
end intrinsic;

function find_a(eta, D, bb, N)
    R2_primes := [x : x in Keys(eta)];
    eta_vals := [eta[x] : x in R2_primes];
    // The 2 is not necessary, but we would like to avoid complications arising at 2
    a_prime_to := [p : p in PrimeDivisors(2*D*N*Norm(bb)) | p notin R2_primes];
    a := CRT(eta_vals cat [1 : p in a_prime_to], R2_primes cat a_prime_to);
    return a;
end function;

function find_mu(theta, eta, a, D, bb, N)
    ZF := Order(bb);
    F := NumberField(ZF);
    R1_primes := R1(D,N);
    R2_primes := R2(D,N);
    other_primes := [p : p in PrimeDivisors(D) | p notin R1_primes cat R2_primes];
    a_primes := [p : p in PrimeDivisors(a)];
    values := [ZF | 0];
    ideals := [Conjugate(bb)];
    values cat:= [theta[p] : p in R1_primes];
    ideals cat:= [PrimeIdealsOverPrime(F,p)[1]^Valuation(D,p) : p in R1_primes];
    values cat:= [0 : p in R2_primes];
    ideals cat:= [p^Valuation(D,p)*ZF : p in R2_primes];
    // TODO: Figure out what happens for p = 2 in other_primes !!
    for p in other_primes do
	frakp := PrimeIdealsOverPrime(F,p)[1];
	ZFmodpv, red := quo<ZF | frakp^Valuation(D,p)>;
	Append(~values, Sqrt(red(N*Norm(bb))));
	Append(~ideals, frakp^Valuation(D,p));
    end for;
    for p in a_primes do
	frakps := PrimeIdealsOverPrime(F,p);
	frakp := frakps[1];
	ZFmodpv, red := quo<ZF | frakp^Valuation(a,p)>;
	if #frakps eq 1 then
	    // inert case
	    // We assume p ne 2 since we can choose a this way
	    U, mU := MultiplicativeGroup(ZFmodpv);
	    Fq := GF(p^2);
	    zeta := PrimitiveElement(Fq);
	    h := hom<ZF -> Fq | zeta^(Eltseq(red(ZF.2)@@mU)[1]) >;
	    h_inv := hom<Fq -> ZFmodpv | mU(U.1)>;
	    // For some reason this doesn't work. However, we can solve it by hands quite simply
	    // is_norm, sol := NormEquation(Fq, h(N*Norm(bb)));
	    // assert is_norm;
	    t := h(N*Norm(bb));
	    Fp := PrimeField(Fq);
	    is_sqr, sol := IsSquare(Fp!t);
	    if is_sqr then
		sol := Fq!sol;
	    else
		is_sqr, sol := IsSquare(Norm(zeta)*Fp!t);
		assert is_sqr;
		sol := zeta * Fq!sol;
	    end if;
	    Append(~values, h_inv(sol)@@red);
	    Append(~ideals, frakp^Valuation(a,p));
	else
	    // split case
	    values cat:= [N*Norm(bb), 1];
	    ideals cat:= [frakp^Valuation(a,p), frakps[2]^Valuation(a,p)];
	end if;	
    end for;
    mu := CRT(values, ideals);
    assert ((Norm(mu) - N*Norm(bb)) mod a*D*Norm(bb)) eq 0;
    return mu;
end function;

intrinsic GetHZComponent(Gamma::GrpHilbert, theta::Assoc, eta::Assoc, N::RngIntElt) -> Mtrx
{Returns a matrix B, such that F_B is a component of F_N on X_Gamma with invariants theta, eta.}	  
    bb := Component(Gamma);
    ZF := Order(bb);
    F := NumberField(ZF);
    D := Discriminant(ZF);
    sigma := Automorphisms(F)[2];
    sqrtD := Sqrt(F!D);
    a := find_a(eta, D, bb, N);
    mu := find_mu(theta, eta, a, D, bb, N);
    b := (N*Norm(bb) - Norm(mu)) div (a*Norm(bb)*D);
    lambda := Norm(bb)^(-1) * mu;
    // Verifying we have an admissible matrix B
    R2_primes := [x : x in Keys(eta)];
    assert lambda in bb^(-1);
    assert &and[GCD(a,p) eq 1 : p in R2_primes];
    assert &and[Norm(bb)*lambda in p^Valuation(D,p)*ZF : p in R2_primes];
    assert &and[b mod p^Valuation(D,p) eq 0 : p in R2_primes];
    g := GCD(a,b);
    if (g gt 1) then
	assert g^(-1)*lambda notin bb^(-1);
    end if;
    B := Matrix([[a*sqrtD, lambda], [-sigma(lambda), Norm(bb)^(-1)*b*sqrtD]]);
    assert IsThetaEqual(Gamma,Theta(Gamma,B),theta);
    assert IsEtaEqual(Gamma,Eta(Gamma,B),eta);
    return B;
end intrinsic;

function is_minus_in_orbit(Gamma, N)
    bb := Component(Gamma);
    ZF := Order(bb);
    F := NumberField(ZF);
    D := Discriminant(ZF);
    d := SquareFree(D);
    not_in_theta := exists(p){p : p in R1(D,N) | d mod p eq 0};
    if not_in_theta then
	return false, "theta", p;
    end if;
    not_in_eta := exists(p){p : p in R2(D,N) | HilbertSymbol(-1,D,p) eq -1};
    if not_in_eta then
	return false, "eta", p;
    end if;
    return true, _, _;
end function;

intrinsic GetAllHZComponents(Gamma::GrpHilbert, N::RngIntElt) -> SeqEnum[AlgMatElt[FldNum]]
{Returns a list of matrices B, such that F_B are representatives for the components of F_N on X_Gamma.}
    if IsHZEmpty(Gamma,N) then
	return [];
    end if;
    ZF := Order(Component(Gamma));
    require Level(Gamma) eq 1*ZF : "Currently only supports trivial level.";
    require AmbientType(Gamma) eq SL_Type : "Currently only supports SL type.";
    thetas := GetPossibleThetas(Gamma,N);
    etas := GetPossibleEtas(Gamma,N);
    is_minus,part,p := is_minus_in_orbit(Gamma,N);
    if not is_minus then
	if (part eq "theta") then
	    theta_p := [x : x in {theta[p] : theta in thetas}];
	    thetas := [theta : theta in thetas | theta[p] eq theta_p[1]];
	else
	    eta_p := [x : x in {eta[p] : eta in etas}];
	    etas := [eta : eta in etas | eta[p] eq eta_p[1]];
	end if;
    end if;
    return [GetHZComponent(Gamma, theta, eta,  N) : theta in thetas, eta in etas];
end intrinsic;

intrinsic Theta(Gamma::GrpHilbert, B::AlgMatElt[FldNum]) -> SeqEnum[Assoc]
{Return the theta invariant of F_B on X_Gamma.}
  bb := Component(Gamma);
  N := Integers()! (Determinant(B)*Norm(bb));
  ZF := Order(bb);
  F := NumberField(ZF);
  sigma := Automorphisms(F)[2];
  D := Discriminant(ZF);
  lambda := B[1,2];
  require &and[B[i,j] eq -sigma(B[j,i]) : i,j in [1..2] | i lt j] : "B should be skew-Hermitian.";
  R1_primes := R1(D,N);
  theta := AssociativeArray(R1_primes);
  for p in R1_primes do
      frakp := PrimeIdealsOverPrime(F,p)[1];
      theta[p] := Norm(bb)*lambda;
  end for;
  return theta;
end intrinsic;

intrinsic IsThetaEqual(Gamma::GrpHilbert, theta1::Assoc, theta2::Assoc) -> BoolElt
{True if the two invariants are equal.}
  bb := Component(Gamma);
  ZF := Order(bb);
  F := NumberField(ZF);
  D := Discriminant(ZF);
  if Keys(theta1) ne Keys(theta2) then return false; end if;
  for p in Keys(theta1) do
      frakp := PrimeIdealsOverPrime(F,p)[1];
      v := Valuation(D,p);
      if (theta1[p] - theta2[p]) notin frakp^v then
	  return false;
      end if;
  end for;
  return true;
end intrinsic;

intrinsic IsEtaEqual(Gamma::GrpHilbert, eta1::Assoc, eta2::Assoc) -> BoolElt
{True if the two invariants are equal.}
  bb := Component(Gamma);
  ZF := Order(bb);
  F := NumberField(ZF);
  D := Discriminant(ZF);
  if Keys(eta1) ne Keys(eta2) then return false; end if;
  for p in Keys(eta1) do
      hilb1 := HilbertSymbol(eta1[p], D, p);
      hilb2 := HilbertSymbol(eta2[p], D, p);
      if (hilb1 ne hilb2) then
	  return false;
      end if;
  end for;
  return true;
end intrinsic;

intrinsic Eta(Gamma::GrpHilbert, B::AlgMatElt[FldNum]) -> SeqEnum[Assoc]
{Return the theta invariant of F_B on X_Gamma.}
  bb := Component(Gamma);
  N := Integers()! (Determinant(B)*Norm(bb));
  ZF := Order(bb);
  F := NumberField(ZF);
  sigma := Automorphisms(F)[2];
  D := Discriminant(ZF);
  sqrtD := Sqrt(F!D);
  a := Integers()!(B[1,1] / sqrtD);
  b := Integers()!(B[2,2] * Norm(bb) / sqrtD);
  lambda := B[1,2];
  require &and[B[i,j] eq -sigma(B[j,i]) : i,j in [1..2] | i lt j] : "B should be skew-Hermitian.";
  R2_primes := R2(D,N);
  eta := AssociativeArray(R2_primes);
  for p in R2_primes do
      if GCD(a,p) eq 1 then
	  eta[p] := HilbertSymbol(a, D, p);
      elif Valuation(b,p) eq Valuation(Norm(bb),p) then
	  eta[p] := HilbertSymbol(b/Norm(bb), Rationals()!D, p);
      else
	  a_new := Rationals()! (a + b/Norm(bb) + (lambda - sigma(lambda)) / sqrtD);
	  assert Valuation(a_new, p) eq 0;
	  eta[p] := HilbertSymbol(a_new, Rationals()!D, p);
      end if;
  end for;
  return eta;
end intrinsic;

intrinsic IsSameComponent(Gamma::GrpHilbert, B1::AlgMatElt[FldNum], B2::AlgMatElt[FldNum]) -> BoolElt
{True if F_B1 and F_B2 belong to the same component on X_Gamma.}
  theta1 :=  Theta(Gamma, B1);
  theta2 := Theta(Gamma, B2);
  sgn := 1;
  eq_theta := IsThetaEqual(Gamma, theta1, theta2);
  if not eq_theta then
      sgn := -1;
      // we negate to check for a minus sign;
      for p in Keys(theta1) do
	  theta1[p] := sgn * theta1[p];
      end for;
      eq_theta := IsThetaEqual(Gamma, theta1, theta2);
      if not eq_theta then
	  return false;
      end if;
  end if;

  eta1 :=  Eta(Gamma, B1);
  eta2 := Eta(Gamma, B2);
  for p in Keys(eta1) do
      eta1[p] := sgn * eta1[p];
  end for;
  
  eq_eta := IsEtaEqual(Gamma, Eta(Gamma,B1), Eta(Gamma,B2));
  
  return eq_eta;
end intrinsic;	  

intrinsic GetHZComponent(Gamma::GrpHilbert, lambda::FldNumElt, comps::SeqEnum[AlgMatElt[FldNum]]) -> RngIntElt
{Return the index of the component F_B where B is a matrix corresponding to lambda with a = 0 on X_Gamma.}
  bb := Component(Gamma);
  ZF := Order(bb);
  F := NumberField(ZF);
  require Level(Gamma) eq 1*ZF : "Currently only supports trivial level.";
  require AmbientType(Gamma) eq SL_Type : "Currently only supports SL type.";
  sigma := Automorphisms(F)[2];
  D := Discriminant(ZF);
  sqrtD := Sqrt(F!D);
  B := Matrix([[0,lambda],[-sigma(lambda), sqrtD / Norm(bb)]]);
  for i->comp in comps do
      if IsSameComponent(Gamma, comp, B) then
	  return i;
      end if;
  end for;
  // This should not happen. If we're here something is wrong!!!
  return 0;
end intrinsic;	  

intrinsic Genera(R::RngOrd) -> Assoc
{Return a representative from each genus of the order.}
  cg, m_cg := ClassGroup(R);
  ncg, m_ncg := NarrowClassGroup(R);
  sq := hom<cg -> ncg | [(m_cg(cg.i)^2)@@m_ncg : i in [1..Ngens(cg)]] >;
  coset_reps := Transversal(ncg, Image(sq));
  ideals := [m_ncg(r) : r in coset_reps];
  symbs := [Genus(bb) : bb in ideals];
  genera := AssociativeArray(symbs);
  for i->symb in symbs do
      genera[symb] := ideals[i];
  end for;
  return genera;
end intrinsic;

intrinsic Genus(bb::RngOrdIdl) -> SeqEnum
{Return the signs representing the genus of the ideal bb.}
  D := Discriminant(Order(bb));
  return [HilbertSymbol(Norm(bb), D, q) : q in PrimeDivisors(D)];
end intrinsic;

intrinsic IsPrincipalGenus(bb::RngOrdIdl) -> BoolElt
{True if bb belongs to the principa genus of its order.}
  return Set(Genus(bb)) eq {1};
end intrinsic;

intrinsic GetHZExceptionalNum(Gamma::GrpHilbert) -> RngIntElt
{Returns number of exceptional HZ divisors if the surface is *not rational*;
 currently only implemented for level 1.}

    require Norm(Level(Gamma)) eq 1 : "Only implemented for level 1";

    A := Norm(Component(Gamma));
    D := Discriminant(Integers(BaseField(Gamma)));
    qs := PrimeDivisors(D);
    Dqs := [PrimeDiscriminant(D,q) : q in qs];
    s := 2*&*[1 + KroneckerSymbol(Dq,A) : Dq in Dqs];
    s +:= &*[1 + KroneckerSymbol(Dq, 2*A) : Dq in Dqs];
    s +:= &*[1 + KroneckerSymbol(Dq, 3*A) : Dq in Dqs] div 2;
    s +:= (1 - KroneckerSymbol(D,3)^2)*
          &*[1 + KroneckerSymbol(Dq,9*A) : Dq in Dqs];
    if D eq 105 then
        s +:= 2;
    end if;
    return s;
end intrinsic;

intrinsic HZLevel(Gamma::GrpHilbert, lambda::FldNumElt) -> RngIntElt
    {Given lambda in b^(-1), returns M such that the HZ divisor associated to lambda is X_0(M).}
    
    require GammaType(Gamma) eq "Gamma0": "Only implemented for Gamma0";
    
    N := Level(Gamma);
    b := Component(Gamma);
    
    ideal1 := Integers() meet b*N*lambda;
    gen1 := Generators(ideal1)[1];
    
    I := Conjugate(BaseField(Gamma)!lambda) * b^(-1);
    denom := Denominator(I);
    gen2 := Generators(Integers() meet I*denom)[1]/denom;
    
    assert gen1*gen2 in Integers();
    return  Integers()!AbsoluteValue((gen1*gen2)/Norm(lambda));
end intrinsic;

function Ma(Gamma, B)
    N := Level(Gamma);
    b := Component(Gamma);
    F := BaseField(Gamma);
    ZF := Integers(F);
    D := Discriminant(ZF);
    sqrtD := Sqrt(F!D);
    sigma := Automorphisms(F)[2];
    
    a := Integers()!(B[1,1] / sqrtD);
    lambda := B[1,2];
    
    basis := Basis(a^(-1)*N*b);
    
    r := [Rationals()!((lambda * x - sigma(lambda*x)) / sqrtD) : x in basis];
    m := [Numerator(x) : x in r];
    n := [Denominator(x) : x in r];
    d := GCD(n[1],n[2]);
    _, _, m2inv := XGCD(d,m[2]);
    assert (m2inv*m[2] - 1) mod d eq 0;
    Ma_basis := [(n[1] div d) * basis[1] - (n[2] div d) * m2inv * m[1] * basis[2], n[2]*basis[2]];
    
    return ideal<ZF | Ma_basis>;
end function;

function left_colon_single(row)
    row := Eltseq(row);
    m := [Numerator(x) : x in row];
    n := [Denominator(x) : x in row];
    d := GCD(n[1],n[2]);
    _, _, m2inv := XGCD(d,m[2]);
    assert (m2inv*m[2] - 1) mod d eq 0;
    basis := [[(n[1] div d), - (n[2] div d) * m2inv * m[1]], [0,n[2]]];
    lat_d := LatticeWithBasis(Matrix(basis));
    assert IsIntegral(lat_d);
    alpha_lat_basis := [(Vector(Rationals(), x), Vector(row)) : x in Basis(lat_d)];
    assert &and[IsIntegral(x) : x in Eltseq(alpha_lat_basis)];
    return lat_d;
end function;

 // find all vectors v in Z^2 such that alpha*v in Z^2
function left_colon(alpha)
    lrows := [left_colon_single(row) : row in Rows(alpha)];
    return &meet lrows;
end function;

intrinsic MatrixRingMap(O::AlgQuatOrd) -> Map
{For a maximal order O in a split quaternion algebra returns an isomorphism from O to the matrix ring over the base.}
  require IsMaximal(O) : "Order must be maximal.";
  B := Algebra(O);
  is_split, _, phi := IsMatrixRing(B : Isomorphism);
  require is_split : "Quaternion algebra must be split.";
  basis := [phi(x) : x in Basis(O)];
  left_O := &meet [left_colon(alpha) : alpha in basis];
  assert &and[&and[IsIntegral(y) : y in Eltseq(Vector(Rationals(),x)*Transpose(alpha))]
	      : alpha in basis, x in Basis(left_O)];
  g := ChangeRing(Transpose(BasisMatrix(left_O)), Rationals());
  assert &and[&and[IsIntegral(y) : y in Eltseq(g^(-1)*phi(x)*g)] : x in Basis(O)];
  M2Q := Codomain(phi);
  return map< B -> M2Q | x :-> g^(-1)*phi(x)*g >;
end intrinsic;

intrinsic HZLevel(Gamma::GrpHilbert, B::AlgMatElt[FldNum]) -> GrpPSL2
{Given a skew-Hermitian matrix B, returns H such that the HZ divisor associated to lambda is X(H).}
    
    require GammaType(Gamma) eq "Gamma0": "Only implemented for Gamma0";

    lambda := B[1,2];

    N := Level(Gamma);
    b := Component(Gamma);
    F := BaseField(Gamma);
    ZF<omega> := Integers(F);
    D := Discriminant(ZF);
    sqrtD := Sqrt(F!D);
    
    a := Integers()!(B[1,1] / sqrtD);
    S_a := Order([F!1, a*F!(omega)]);
    assert Norm(Conductor(S_a)) eq Abs(a);

    M_a := Ma(Gamma, B);
    Q<i,j> := QuaternionAlgebra(Rationals(), D, -Determinant(B)/D);
    F_to_Q := hom<F -> Q | i>;
    basis_O_B := [F_to_Q(s) : s in Basis(S_a)] cat [(F_to_Q(lambda / sqrtD) + j) * F_to_Q(m) : m in Basis(M_a)];
    O_B := QuaternionOrder(basis_O_B);
    
    N_B := Level(O_B);

    if (N_B eq 1) then
	return Gamma0(1);
    end if;
    
    phi := MatrixRingMap(MaximalOrder(O_B));

    M2ZN := MatrixRing(Integers(N_B),2);
    // !! TODO : This is highly inefficient, needs to find some way to do it efficiently.
    // However, Magma refuses to do almost anything with the type M2ZN
    all_elts := {M2ZN!&+[a[i]*phi(Basis(O_B)[i]) : i in [1..4]] : a in CartesianPower([0..N_B-1],4)};
    coset_reps := [x : x in all_elts | Determinant(x) ne 0];
    H := sub<GL(2,Integers(N_B)) | coset_reps>;
    
    return PSL2Subgroup(H);
end intrinsic;

intrinsic HZGenus(Gamma::GrpHilbert, lambda::FldNumElt) -> RngIntElt
{}
    M := HZLevel(Gamma, lambda);
    return Genus(Gamma0(M)); 
end intrinsic;

intrinsic HZGenus(Gamma::GrpHilbert, B::AlgMatElt[FldNum]) -> RngIntElt
{}
    G_B := HZLevel(Gamma, B);
    return Genus(G_B); 
end intrinsic;

intrinsic HZVolume(Gamma::GrpHilbert, lambda::FldNumElt) -> FldRatElt
    {}
    M := HZLevel(Gamma, lambda);
    return (1/6)*Index(Gamma0(M));
end intrinsic;

intrinsic HZVolume(Gamma::GrpHilbert, B::AlgMatElt[FldNum]) -> FldRatElt
{}
    G_B := HZLevel(Gamma, B);
    return (1/6)*Index(G_B);
end intrinsic;

intrinsic HZEllipticIntersection(Gamma::GrpHilbert, lambda::FldNumElt) -> FldRatElt
    {}
    M := HZLevel(Gamma, lambda);
    sign := Signature(Gamma0(M))[2];
    count := 0;
    for s in sign do
        if s eq 3 then
            count := count + 1;
        end if;
    end for;
    return (1/3)*count;
 end intrinsic;

intrinsic HZEllipticIntersection(Gamma::GrpHilbert, B::AlgMatElt[FldNum]) -> FldRatElt
{}
    G_B := HZLevel(Gamma, B);
    sign := Signature(G_B)[2];
    count := 0;
    for s in sign do
        if s eq 3 then
            count := count + 1;
        end if;
    end for;
    return (1/3)*count;
end intrinsic;

intrinsic HZc1Intersection(Gamma::GrpHilbert, lambda::FldNumElt) -> RngIntElt
    {Computes c1*F_B for F_B associated with lambda using Corollary VII.4.1.}
    return -2*HZVolume(Gamma, lambda) + HZEllipticIntersection(Gamma, lambda) + #Cusps(Gamma0(HZLevel(Gamma, lambda)));
end intrinsic;

intrinsic HZc1Intersection(Gamma::GrpHilbert, B::AlgMatElt[FldNum]) -> RngIntElt
{Computes c1*F_B for F_B associated with lambda using Corollary VII.4.1.}
    return -2*HZVolume(Gamma, B) + HZEllipticIntersection(Gamma, B) + #Cusps(HZLevel(Gamma, B));
end intrinsic;

intrinsic IsExceptional(Gamma::GrpHilbert, B::AlgMatElt[FldNum]) -> BoolElt
 {Given Gamma = Gamma_0(N) and B, checks if F_B is an exceptional curve on X_Gamma.}
    if HZc1Intersection(Gamma, B) eq 1 and HZGenus(Gamma, B) eq 0 then
        return true;
    else 
        return false;
    end if;
end intrinsic;

intrinsic IsExceptional(Gamma::GrpHilbert, lambda::FldNumElt) -> BoolElt
    {Given Gamma = Gamma_0(N) and lambda, checks if F_lambda is an exceptional curve on X_Gamma.}
    if HZc1Intersection(Gamma, lambda) eq 1 and HZGenus(Gamma, lambda) eq 0 then
        return true;
    else 
        return false;
    end if;
end intrinsic;

intrinsic EllipticMatricesQ(G::GrpHilbert) -> SeqEnum
    {Given G = Gamma0(N) in SL_2(Z), returns list of elliptic matrices in G.}
    elist := EllipticPoints(G);
    glist := [G|Stabilizer(e,G)  : e in elist];
    return glist;
end intrinsic;

intrinsic EllipticMatrices(Gamma::GrpHilbert, lambda::FldNumElt) -> SeqEnum
    {Returns a list of elements in Gamma corresponding to the elliptic points on F_lambda.}
    M := HZLevel(Gamma, lambda);
    G := Gamma0(M);
    glist := EllipticMatricesQ(G);
    
    I := Conjugate(BaseField(Gamma)!lambda)*Component(Gamma)^(-1);
    denom := Denominator(I);
    x := Generators(denom*I meet Integers())[1]/denom;
    y := Conjugate(BaseField(Gamma)!lambda)^(-1)*x;
    
    Gammalist := [ Matrix(2, [y,0,0,1])*Matrix(g)* Matrix(2, [y^(-1),0,0,1]) : g in glist];
    return Gammalist;
end intrinsic;

intrinsic Lambdas(Gamma::GrpHilbert) -> SeqEnum
    {List of lambdas such that F_lambda is exceptional on X_Gamma; we think this list is exhaustive.}
    F := BaseField(Gamma);
    D := Discriminant(F);
    DD := &*[ PrimeIdealsOverPrime(F, p[1])[1]^(p[2]) : p in Factorization(D)];
        
    ZF := Integers(F);
    N := Level(Gamma);
    b := Component(Gamma);
    binv := b^(-1);
    denom := Denominator(binv);
    I := binv*denom;
    assert IsIntegral(I);
    I := ZF!!I;
    
    list := [];
    
    ZF_mod_N, q := quo<ZF | N*DD>;
    residues := [x@@q : x in ZF_mod_N];
    
    mus := { CRT( I, N*DD, ZF!0, x ) : x in residues | not x eq 0 } join {Generators(DD*N*I)[1]};
    
    lambdas := [ mu/denom : mu in mus ] ;

    lambdas0 := [lambda : lambda in lambdas | IsExceptional(Gamma, lambda)];
    
    //Clean up the list of lambdas further:
    //if lambda_1 = -lambda_2, only keep one of them.
    
    newlambdas := [];

    for lambda in lambdas0 do
        add := true;
        if (-lambda in newlambdas) then
            add := false;
        else
            l := Norm(lambda);
            for f in Factorization(Numerator(l)) do
                if f[2] ge 1 then
                    if IsIntegral(F!(lambda/f[1])) and IsIntegral(F!(Conjugate(F!lambda)/f[1])) then
                        add := false;
                    end if;
                end if;
            end for;
        end if;
        
        if add then
            Append(~newlambdas, lambda);
        end if;
    end for;
    return newlambdas;
end intrinsic;

//This function still needs some testing!

intrinsic RelevantEllipticCycles(Gamma::GrpHilbert, list::SeqEnum) -> SeqEnum
    {Given a list of lambdas and Gamma, compute a list of elliptic cycles (labeled by their self-intersection numbers) that intersect at least one F_lambda, and which lambdas they intersect.
    The output is a list of lists:
    [-2, -3, -2, ...]: self-intersection numbers of elliptic cycles,
    [1, 0, 0, 1, ...]: intersection of F_(lambda_1) which each elliptic cycles,
    [0, 1, 0, 0, ...]: intersection of F_(lambda_2) which each elliptic cycles,
    etc.
    }
    
    lambdalist := list;
    
    ellipticlist := [];
    selfintlist := [];

    intmatrix := [];
    
    for lambda in lambdalist do
        intlist := [0 : i in ellipticlist];
        E := EllipticMatrices(Gamma, lambda);
        for e in E do
            assert not e in [Matrix(2, [1, 0, 0, 1]), Matrix(2, [-1, 0, 0, -1])];
            new := true;
            for i in [1 .. #ellipticlist] do
                d := ellipticlist[i];
                if (e eq d) or (-e eq d) or (e^2 eq d) or (-e^2 eq d) then
                    // e is equal to d, i.e. F_lambda intersects it
                    intlist[i] := 1;
                    new := false;
                end if;
            end for;
            if new then
                // e is a new elliptic point!
                Append(~ellipticlist, e);
                Append(~intlist, 1);
                if e^2 in [Matrix(2, [1, 0, 0, 1]), Matrix(2, [-1, 0, 0, -1])] then
                    Append(~selfintlist, -2);
                elif e^3 in [Matrix(2, [1, 0, 0, 1]), Matrix(2, [-1, 0, 0, -1])] then
                    Append(~selfintlist, -3);
                end if;
            end if;
        end for;
        Append(~intmatrix, intlist);
    end for;
    
    //clean up final matrix
    
    maxlength := #(intmatrix[#intmatrix]);
        
    for i in [1 .. #intmatrix] do
        list := intmatrix[i];
        if #list le (maxlength - 1) then
            intmatrix[i] := list cat [0 : j in [1 .. (maxlength - #list)]];
        end if;
    end for;

    
    
    return [* ellipticlist,selfintlist, intmatrix *];
end intrinsic;

// This is not enough. In order to get components correctly in the presence of level structure, we should
// be able to construct explicit isometries transforming one Hermitian lattice to another, so that we will be
// able to check how they act on a distinguished line.

function bart(g)
    F := BaseRing(g);
    sigma := Automorphisms(F)[2];
    return Parent(g)![sigma(x) : x in Eltseq(Transpose(g))];
end function;

function Orthogonalize(C)
    assert (Nrows(C) eq 2) and (Ncols(C) eq 2);
    a := C[1,1];
    b := C[1,2];
    c := C[2,2];
    F := BaseRing(C);
    sigma := Automorphisms(F)[2];
    assert (C[2,1] eq sigma(b)) and (sigma(a) eq a) and (sigma(c) eq c);
    if (a eq 0) and (c eq 0) then
	T := Matrix(F, [[1,b],[1,-b]]);
    elif (a eq 0) then
	S := Matrix(F, [[0,1],[-1,0]]);
	_, T := Orthogonalize(S*C*bart(S));
	T := T*S;
    else
	T := Matrix(F, [[1,0],[-sigma(b),a]]); 
    end if;
    C_orth := T*C*bart(T);
    assert (C_orth[1,2] eq 0) and (C_orth[2,1] eq 0);
    return C_orth, T;
end function;

function FindIsometry(B1, B2)
    // we start by constructing lattices for both in the same Hermitian space
    F := BaseRing(B1);
    ZF := Integers(F);
    D := Discriminant(ZF);
    sqrtD := Sqrt(F!D);
    C1 := sqrtD*B1;
    C2 := sqrtD*B2;
    D1, T1 := Orthogonalize(C1);
    D2, T2 := Orthogonalize(C2);
    // !! TODO : Is that true? Maybe just away from the ramified primes? maybe up to a constant?
    assert D1 eq D2;
    bc := T1*T2^(-1);
    return bc;
end function;


