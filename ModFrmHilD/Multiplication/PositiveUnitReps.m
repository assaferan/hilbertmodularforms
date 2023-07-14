/////// **************** PUBLIC FUNCTIONS **************** /////// 

intrinsic FunDomainRep(nu::FldNumElt : lattice := "tot_pos", Precision := 100) -> FldNumElt, FldNumElt
  {
    inputs:
      nu: Number field element
    returns: 
      An element nu' in the fundamental domain and a 
      totally positive unit eps such that nu = eps * nu'

    We compute this by passing to the log-Minkowski domain,
    writing the log-embedding of nu in a basis spanned by 
    the log-positive units (which lie on the trace-zero 
    hyperplane) and (1 ... 1). We can forget the last coordinate
    because we are interested in the log-positive unit action.
    We add 1/2 to everything and then take floor function - this serves
    to find the product of positive units necessary to bring the 
    log-embedding of nu into the balanced fundamental parallelepiped 
    spanned by the log-positive units. 
  }

  F := NumberField(Parent(nu));

  if IsZero(nu) then
    return F!0, F!1;
  end if;

  n := Degree(F);
  if lattice eq "tot_pos" then
    epses := TotallyPositiveUnitsGenerators(F);
  elif lattice eq "squares" then
    epses := [eps^2 : eps in UnitsGenerators(F)];
  else
    require 0 eq 1 : "Invalid option for lattice - the options are 'tot_pos' and 'squares'.";
  end if;

  log_nu := ForgetTraceLogEmbed(nu, epses : Precision := Precision);

  THRESHOLD := 10^-10;
  nu_prime := nu;
  for i in [1 .. (n-1)] do
    // we add a threshold because Magma does some silly things
    // with 0.9999999 != 1 and we want points on the 
    // "upper wall" to be reduced to the lower wall
    eps_i_shift := Floor(log_nu[i] + 1/2 + THRESHOLD);
    nu_prime :=  nu_prime * epses[i] ^ -eps_i_shift;
  end for;
  eps := nu/nu_prime;
  return nu_prime, eps;
end intrinsic;

intrinsic FunDomainRep(nu::RngElt : lattice := "tot_pos", Precision := 100) -> FldNumElt, FldNumElt
  {
    inputs:
      nu: Element of the ring of integers of a number field.
    returns: 
      An element nu' in the fundamental domain and a 
      totally positive unit eps such that nu = eps * nu'
  }
  ZF := Parent(nu);
  F := NumberField(ZF);
  return FunDomainRep(F!nu : lattice := lattice, Precision := Precision); 
end intrinsic;

/////// **************** HELPER FUNCTIONS **************** /////// 

intrinsic EmbedNumberFieldElement(nu::FldNumElt : Precision := 100) -> SeqEnum
  {}
  F := Parent(nu);
  return [Evaluate(nu, place : Precision := Precision) : place in InfinitePlaces(F)];
end intrinsic;

intrinsic EmbedNumberFieldElement(nu::RngOrdElt : Precision := 100) -> SeqEnum
  {}
  F := Parent(nu);
  return [Evaluate(F!nu, place : Precision := Precision) : place in InfinitePlaces(F)];
end intrinsic;

intrinsic ForgetTraceLogBasis(F::FldNum, A::SeqEnum[FldReElt], epses::SeqEnum[RngOrdElt] : Precision := 100) -> SeqEnum
  {
    input: 
      A: A sequence of real numbers [a_1, ..., a_n],
         thought of as a point in log-Minkowski space
           of the field F. 
      epses: A sequence of (n-1) totally positive units which span a lattice
        in the trace-zero hyperplane of log-Minkowski space
    returns: 
      The first (n-1) coordinates of the A 
      after writing it in the basis spanned by
      the log-Minkowski embeddings of eps_1, eps_2, ..., eps_(n-1),
      and [1, 1, ..., 1, 1], where eps_i is the ith 
      generator of the group totally positive units. 
      
      Essentially, we forget about the trace of A
      and write the 'trace zero' part using the given
      units as a basis. 
  }
  B_rows := [[Log(x) : x in EmbedNumberFieldElement(eps : Precision := Precision)] : eps in epses];
  Append(~B_rows, [1 : i in [1 .. #A]]);
  B := Matrix(B_rows);
  v := Vector(A) * B^-1;

  return Prune([v[i] : i in [1 .. Dimension(Parent(v))]]);
end intrinsic;

intrinsic ForgetTraceLogEmbed(nu::RngOrdElt, epses::SeqEnum[RngOrdElt] : Precision := 100) -> SeqEnum[ModTupFldElt]
  {
    input:
      nu: an element of ZF for F a totally real number field of degree n
      epses: a sequence of (n-1) totally positive units which span a lattice
        in the trace-zero hyperplane of Log-Minkowski space
    returns:
      If n is the degree of F, the (n-1)-dimensional vector corresponding to 
      taking the log-Minkowski embedding of nu and applying ForgetTraceLogBasis.
  }
  R := Parent(nu);
  F := NumberField(R);
  return ForgetTraceLogBasis(F, [Log(x) : x in EmbedNumberFieldElement(F!nu : Precision := Precision)], epses : Precision := Precision);
end intrinsic;

intrinsic ForgetTraceLogEmbed(nu::FldNumElt, epses::SeqEnum[RngOrdElt] : Precision := 100) -> SeqEnum[ModTupFldElt]
  {
    input:
      nu: a totally positive element of a totally real number field F.
      epses: a sequence of (n-1) totally positive units which span a lattice
        in the trace-zero hyperplane of Log-Minkowski space
    returns:
      If n is the degree of F, the (n-1)-dimensional vector corresponding to 
      taking the log-Minkowski embedding of nu and applying ForgetTraceLogBasis.
  }
  F := Parent(nu);
  return ForgetTraceLogBasis(F, [Log(x) : x in EmbedNumberFieldElement(F!nu : Precision := Precision)], epses);
end intrinsic;
