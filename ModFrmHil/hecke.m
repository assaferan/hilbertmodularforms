// Copied from ModFrmHil/hecke.m and modified

freeze;

import "copypaste/definite.m" : HeckeOperatorDefiniteBig,
                                AtkinLehnerDefiniteBig,
                                DegeneracyDown1DefiniteBig,
				DegeneracyDownpDefiniteBig;
import "copypaste/hackobj.m" : IsBianchi, TopAmbient;
import "copypaste/hecke.m" : basis_is_honest, basis_matrix, make_ideal, restriction;
import "diamond.m" : DiamondOperatorDefiniteBig;

debug := false;

please_report :=
"\nPlease send this example to magma-bugs@maths.usyd.edu.au" *
"\n\nHint: to print the entire input of this session, type %P\n";

function hecke_matrix_field(M : hack := true)
  if assigned M`hecke_matrix_field then
    return M`hecke_matrix_field;
  elif IsBianchi(M) or not IsDefinite(M) then
    return Rationals();
  else
      if hack then
	  // hack begins
	  return TopAmbient(M)`weight_base_field;
	  // hack ends
      else
	  return Ambient(M)`weight_base_field;
      end if;
  end if;
end function;

////////////////////////////////////////////////////////////////////////////////////////
// Interface for operators (handles caching and calls the appropriate raw function)
////////////////////////////////////////////////////////////////////////////////////////

function checks(M, _p, op : hack := true)
  p := make_ideal(_p);

  if not (ISA(Type(p), RngOrdIdl) and NumberField(Order(p)) eq BaseField(M)) 
     and not (Type(p) eq RngInt and BaseField(M) eq Rationals()) 
  then
    return false, "The second argument should be an ideal of the base field of the first argument", p;
  end if;

  if IsBianchi(M) then
    if op eq "Hecke" then
      return true, _, p;
    else
      return false, "Not implemented for spaces of Bianchi forms", p;
    end if;
  end if;
    
  if op notin {"Hecke", "AL"} and not IsDefinite(M) then
    return false, "Operator not implemented (for spaces computed with the indefinite algorithm)", p;
  end if;

  if hack then
      // hack begins
      if op notin {"AL", "Diamond"} and not IsPrime(p) then
	  // hack ends
	  return false, "The second argument must be prime", p;
      end if;
  else
      if op ne "AL" and not IsPrime(p) then
	  return false, "The second argument must be prime", p;
      end if;
  end if;

  if hack then
      // hack begins
      if op notin {"Hecke", "Diamond"} then
	  // hack ends
	  // must divide the Eichler level
	  if not Level(M) subset p * make_ideal(Discriminant(QuaternionOrder(M))) then
	      if not Level(M) subset p then
		  return false, "The second argument must divide the level of the space", p;
	      end if;
	      return false, "Operator not implemented in this case (ideal is not coprime to the"
			    *" discriminant of the quaternion order used to compute this space)", p;
	  end if;
	  if op ne "AL" and Seqset(Weight(M)) ne {2} then
	      return false, "Operator is currently implemented only for parallel weight 2", p;
	  end if;
      end if;
  else
      if op ne "Hecke" then
	  // must divide the Eichler level
	  if not Level(M) subset p * make_ideal(Discriminant(QuaternionOrder(M))) then
	      if not Level(M) subset p then
		  return false, "The second argument must divide the level of the space", p;
	      end if;
	      return false, "Operator not implemented in this case (ideal is not coprime to the"
			    *" discriminant of the quaternion order used to compute this space)", p;
	  end if;
	  if op ne "AL" and Seqset(Weight(M)) ne {2} then
	      return false, "Operator is currently implemented only for parallel weight 2", p;
	  end if;
      end if;
  end if;

  return true, _, p;
end function;

function operator(M, p, op : hack := true)
  assert op in {"Hecke", "AL", "DegDown1", "DegDownp", "Diamond"};

  // Check if cached on M
  cached, Tp := IsDefined(eval "M`"*op, p);
  if cached then 
    return Tp;
  end if;

  if Dimension(M : UseFormula:=false) eq 0 then // gets cached dimension or computes the space

    Tp := ZeroMatrix(Integers(), 0, 0); 

  elif assigned M`basis_matrix_wrt_ambient then 

    // (TO DO: is this always better than getting it directly from the big operator?)
    bm := M`basis_matrix_wrt_ambient;
    bmi := M`basis_matrix_wrt_ambient_inv;
    Tp_amb := operator(M`Ambient, p, op);
    Tp_amb := ChangeRing(Tp_amb, BaseRing(bm));
    Tp := bm * Tp_amb * bmi;

    if debug and basis_is_honest(M) and Norm(p + Level(M)) eq 1 then 
      // check Tp really preserves M as a subspace of M`Ambient
      assert Rowspace(bm * Tp_amb) subset Rowspace(bm); 
    end if;

  elif IsBianchi(M) then

    // Always compute and store operator on ambient

    bool, MA := HasAttribute(M, "Ambient");

    if not bool then
      return HeckeMatrixBianchi(M, p);
    end if;

    assert not assigned MA`Ambient;

    Tp := HeckeMatrixBianchi(MA, p);

    bm := M`basis_matrix_wrt_ambient;
    bmi := M`basis_matrix_wrt_ambient_inv;
    return bm * Tp * bmi;

  elif IsDefinite(M) then 

    MA := TopAmbient(M);
    case op:
      when "Hecke"   : Tp_big := HeckeOperatorDefiniteBig(MA, p);
      when "AL"      : Tp_big := AtkinLehnerDefiniteBig(MA, p);
      when "DegDown1": Tp_big := DegeneracyDown1DefiniteBig(MA, p);
      when "DegDownp": Tp_big := DegeneracyDownpDefiniteBig(MA, p);
      when "Diamond" : Tp_big := DiamondOperatorDefiniteBig(MA, p);		     
    end case;
    Tp := restriction(M, Tp_big);

  else // indefinite quat order

    disc := make_ideal(Discriminant(QuaternionOrder(M)));
    MA := TopAmbient(M);
    assert disc eq make_ideal(NewLevel(MA));
    N := Level(M)/disc;

    Gamma := FuchsianGroup(QuaternionOrder(M));
    case op:
      when "Hecke" : Tp_big := HeckeMatrix(Gamma, N, p);
      when "AL"    : Tp_big := HeckeMatrix(Gamma, N, p : UseAtkinLehner);
    end case;
    bm, bmi := basis_matrix(M);
    Tp := restriction(M, Tp_big);

  end if;

  if assigned M`hecke_matrix_field then
    bool, Tp := CanChangeRing(Tp, M`hecke_matrix_field);
    error if not bool, 
         "The hecke_matrix_field seems to be wrong!\n" * please_report;
  end if;

  if debug then
    // check commutativity
    bad := Level(M) / NewLevel(M);
    new := Minimum(bad) eq 1;
    for l in Keys(M`Hecke) do 
      if new or Minimum(l + bad) eq 1 then
        Tl := M`Hecke[l];
        assert Tl*Tp eq Tp*Tl; 
      end if;
    end for; 
  end if;

  // Cache
  // (for definite ambient, big matrix is cached instead)
// TO DO: hecke_algebra etc checks cache directly
  //if not (IsDefinite(M) and not assigned M`Ambient) then
  if hack then
    case op:
      when "Hecke"    : M`Hecke[p]    := Tp;
      when "AL"       : M`AL[p]       := Tp;
      when "DegDown1" : M`DegDown1[p] := Tp;
      when "DegDownp" : M`DegDownp[p] := Tp;
      // hack begins
      // TO DO : we just need to remember the class group representative
      // However, need to cache also the map to the class group to make sure it is consistent.			
      when "Diamond"  : M`Diamond[p]  := Tp;
      // hack ends
    end case;
  else
    case op:
      when "Hecke"    : M`Hecke[p]    := Tp;
      when "AL"       : M`AL[p]       := Tp;
      when "DegDown1" : M`DegDown1[p] := Tp;
      when "DegDownp" : M`DegDownp[p] := Tp;
    end case;
  end if;
//end if;

  return Tp;
end function;
