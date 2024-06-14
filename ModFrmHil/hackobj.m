// copied from ModFrmHil/hackobj.m and modified
// freeze;

import !"Geometry/ModFrmHil/hackobj.m" : ideal_print_on_one_line, IsBianchi, is_cached_hmf, set_quaternion_order;

/**************** New Attributes **********************/

declare attributes ModFrmHil : Diamond, UnitCharacter;

/********************************************************/

// function copy pasted from hackobj.m and modified

function HMF0(F, N, Nnew, Chi, k, C : hack := true, eps := 1)
  M := New(ModFrmHil);
  M`Field := F;
  M`Level := N;
  M`NewLevel := Nnew;
  M`DirichletCharacter := Chi;
  // hack begins
  if hack then
      if IsOne(eps) then
	  eps := WeightUnitCharacter(F, k);
      end if;
      M`UnitCharacter := eps;
  end if;
  // hack ends
  M`Weight := k;
  M`CentralCharacter := C;
  assert C eq Max(k) - 2; // currently
  M`is_cuspidal := true; // always true, currently
  M`Hecke    := AssociativeArray();
  M`HeckeBig := AssociativeArray();
  M`HeckeBigColumns := AssociativeArray();
  M`HeckeCharPoly := AssociativeArray();
  M`AL       := AssociativeArray();
  M`DegDown1 := AssociativeArray();
  M`DegDownp := AssociativeArray();
  // hack begins
  if hack then
      M`Diamond := AssociativeArray();
  end if;
  // hack ends
  if forall{w : w in k | w eq 2} then
    M`hecke_matrix_field := Rationals();
    M`hecke_matrix_field_is_minimal := true;
  else
    M`hecke_matrix_field_is_minimal := false;
  end if;
  return M;
end function;

// function copy pasted from hackobj.m and modified

function HMF(F, N, k : Chi:=1, QuaternionOrder:=0, hack := true, eps := 1)

    // TO DO: errors should be passed back to the calling intrinsic

    if Chi cmpeq 1 then
	bool, M := is_cached_hmf(QuaternionOrder, F, N, k);
	if bool then
	    return M;
	end if;
    end if;

    bool, _, _, C := IsArithmeticWeight(F, k); assert bool; // already checked

    M := HMF0(F, N, 1*Integers(F), Chi, k, C : hack := hack, eps := eps);
    
    if QuaternionOrder cmpne 0 then 
	ok, message := IsSuitableQuaternionOrder(QuaternionOrder, M);
	error if not ok, message;
	set_quaternion_order(M, QuaternionOrder); // cache on QuaternionOrder
    end if;
    
    // cache on F
    if assigned F`ModFrmHils then
	if IsDefined(F`ModFrmHils, N) then
	    Append(~F`ModFrmHils[N], M);
	    assert M in F`ModFrmHils[N];
	else
	    F`ModFrmHils[N] := [* M *];
	end if;
    end if;

    return M;
end function;

/**************** Modified intrinsic *******************/
intrinsic Print(x::ModFrmHil, level::MonStgElt : hack := true)
{}
  F := BaseField(x);

  assert assigned x`is_cuspidal;

  if x`is_cuspidal and assigned x`HeckeIrreducible and x`HeckeIrreducible then
    printf "Cuspidal newform space ";
  elif x`is_cuspidal and IsNew(x) and Norm(Level(x)) ne 1 then
    printf "New cuspidal space ";
  elif x`is_cuspidal then
    printf "Cuspidal space ";
  else 
    printf "Space ";
  end if;

  if IsBianchi(x) then
    printf "of Bianchi modular forms";
  else
    printf "of Hilbert modular forms";
  end if;

  if level ne "Minimal" then 
    printf " over";
    printf "\n    %o", BaseField(x);
    printf "\n    Level: "; 
    _ := ideal_print_on_one_line(Level(x), level); 
    if Norm(NewLevel(x)) ne 1 then 
      printf "\n    New level: ";
      _ := ideal_print_on_one_line(NewLevel(x), level); 
    end if;
    if x`DirichletCharacter cmpne 1 then
      printf "\n    Dirichlet character: %o", x`DirichletCharacter;
    end if;
    // hack begins
    if hack then
	if not IsOne(x`UnitCharacter) then
	    printf "\n    Unit character: %o", x`UnitCharacter;
	end if;
    end if;
    // hack ends
    printf "\n    Weight: %o", Weight(x);
    if assigned x`Dimension then 
      printf "\n    Dimension %o", x`Dimension; 
    end if;
  end if;
  if level eq "Maximal" and assigned x`QuaternionOrder then 
    O := x`QuaternionOrder;
    printf "\ncomputed as automorphic forms on %o order in %o quaternion algebra of discriminant ", 
           IsMaximal(O) select "maximal" else "Eichler", 
           IsDefinite(Algebra(O)) select "definite" else "indefinite";
    _ := ideal_print_on_one_line( Discriminant(Algebra(O)), level);
  end if;
end intrinsic;
/******************** end of modified intrinsic ****************************/

/**************** New intrinsics **********************/

intrinsic HilbertCuspForms(F::FldNum, N::RngOrdIdl, chi::GrpHeckeElt,
			   k::SeqEnum[RngIntElt] :
			   QuaternionOrder:=0, eps := 1) -> ModFrmHil
{The space of Hilbert modular forms over the totally real number field F,
    with level N , character chi and weight k (or parallel weight 2, if k is not specified).
 Here N should be an ideal in the maximal order of F, chi should be a Hecke character and k should be a
 sequence of integers.
 If the optional argument QuaternionOrder is specified, this order
 will be used for all computations of the space.}

  require NumberField(Order(N)) eq F :
         "The level N must be an ideal in the base field";
  require IsAbsoluteField(F) :
         "The base field F must be an absolute extension of Q";
  require IsTotallyReal(F) :
         "The base field F must be totally real";
  require #k eq Degree(F) :
         "The weight k should be a sequence of d integers, where d is the degree of the field";
  // TODO : Do we still want to leave this?
  require IsArithmeticWeight(F, k) :
         "The weight should be a sequence of integers that are all at least 2, and all of the same parity";
  require IsCompatibleWeight(chi, k) :
         "The weight should be compatible with the character.";

  return HMF(F, N, k : Chi := chi, QuaternionOrder:=QuaternionOrder, eps := eps);
end intrinsic;

intrinsic HilbertCuspForms(F::FldNum, N::RngOrdIdl, chi::GrpHeckeElt,
			   k::RngIntElt : QuaternionOrder:=0, eps := 1) -> ModFrmHil
{"} // "
  require NumberField(Order(N)) eq F :
         "The level N must be an ideal in the base field";
  require IsAbsoluteField(F) :
         "The base field F must be an absolute extension of Q";
  require IsTotallyReal(F) :
         "The base field F must be totally real";
  require IsCompatibleWeight(chi, k) :
         "The weight should be compatible with the character.";

  k := [k : i in [1..Degree(F)]];
  return HMF(F, N, k : Chi := chi, QuaternionOrder:=QuaternionOrder, eps := eps);
end intrinsic;

intrinsic HilbertCuspForms(F::FldNum, N::RngOrdIdl, chi::GrpHeckeElt
			   : QuaternionOrder:=0, eps := 1)
       -> ModFrmHil
{"} // "
  require NumberField(Order(N)) eq F :
         "The level N must be an ideal in the base field";
  require IsAbsoluteField(F) :
         "The base field F must be an absolute extension of Q";
  require IsTotallyReal(F) :
         "The base field F must be totally real";
  require IsCompatibleWeight(chi, 2) :
         "The weight should be compatible with the character.";

  k := [2 : i in [1..Degree(F)]];
  return HMF(F, N, k : Chi := chi, QuaternionOrder:=QuaternionOrder, eps := eps);
end intrinsic;

intrinsic HilbertCuspForms(F::FldRat, N::RngInt, chi::GrpHeckeElt,
			   k::RngIntElt : QuaternionOrder:=0, eps := 1)
       -> ModFrmHil
{The space of modular forms over the rationals with level N, character chi and weight k
 (or weight 2, if k is not specified).
 If the optional argument QuaternionOrder is specified, this quaternion order
 will be used for all computations of the space.}

  require k eq 2 :
    "Over Rationals(), only implemented for weight 2.  Use RationalsAsNumberField() instead.";
  return HMF(F, N, [k] : Chi := chi, QuaternionOrder:=QuaternionOrder, eps := eps );
end intrinsic;

intrinsic HilbertCuspForms(F::FldRat, N::RngIntElt, chi::GrpHeckeElt,
		           k::RngIntElt : QuaternionOrder:=0, eps := 1) -> ModFrmHil
{"} // "
  require k eq 2 :
    "Over Rationals(), only implemented for weight 2.  Use RationalsAsNumberField() instead.";
  return HMF(F, N*Integers(), [k] : Chi := chi, QuaternionOrder:=QuaternionOrder, eps := eps );
end intrinsic;

intrinsic HilbertCuspForms(F::FldRat, N::RngInt, chi::GrpHeckeElt,
		           k::SeqEnum[RngIntElt] : QuaternionOrder:=0, eps := 1) -> ModFrmHil
{"} // "
  require k eq [2] :
    "Over Rationals(), only implemented for weight 2.  Use RationalsAsNumberField() instead.";
  return HMF(F, N, k : Chi := chi, QuaternionOrder:=QuaternionOrder, eps := eps );
end intrinsic;

intrinsic HilbertCuspForms(F::FldRat, N::RngIntElt, chi::GrpHeckeElt,
			   k::SeqEnum[RngIntElt] : QuaternionOrder:=0, eps := 1) -> ModFrmHil
{"} // "
  require k eq [2] :
    "Over Rationals(), only implemented for weight 2.  Use RationalsAsNumberField() instead.";
  return HMF(F, N*Integers(), k : Chi := chi, QuaternionOrder:=QuaternionOrder, eps := eps );
end intrinsic;

intrinsic HilbertCuspForms(F::FldRat, N::RngInt, chi::GrpHeckeElt : QuaternionOrder:=0, eps := 1) -> ModFrmHil
{"} // "
  return HMF(F, N, [2] : Chi := chi, QuaternionOrder:=QuaternionOrder, eps := eps );
end intrinsic;

intrinsic HilbertCuspForms(F::FldRat, N::RngIntElt, chi::GrpHeckeElt : QuaternionOrder:=0, eps := 1) -> ModFrmHil
{"} // "
  return HMF(F, N*Integers(), [2] : Chi := chi, QuaternionOrder:=QuaternionOrder, eps := eps );
end intrinsic;

/************** end of new intrinsics ****************/
