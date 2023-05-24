intrinsic RationalityCriterion(Gamma) -> BoolElt
{Checks whether the Rationality Criterion is satisfied.
 Note 1: Only implemented for Gamma0(N) level.
 Note 2: only considers diagonal HZ curves, it could be refined by including non-diagonal ones.}

    require GammaType(Gamma) eq "Gamma0": "Only implemented for Gamma0";

    F := BaseField(Gamma);

    //Make a list of intersection numbers of cuspidal resolution cycles.
    res := CuspsWithResolution(Gamma);
    self_int_res := [];
    for x in res do
      for y in [1..x[4]] do
          self_int_res cat:= x[3];
      end for;
    end for;

    LevelList := [];

    //Make a list of possible exceptional Hirzebruch--Zagier divisors.
    if Norm(Level(Gamma)) eq 1 then //vdG VII.4 gives the following
        A := Component(Gamma);
        if Norm(A) eq 1 then
        Append(~LevelList, 1);
        Append(~LevelList, 4);
        Append(~LevelList, 9);
        end if;

        if NormEquation(F, 2*Norm(A)) then //2 is the norm of an ideal in the genus of A.
        Append(~LevelList, 2);
        end if;

        if NormEquation(F, 3*Norm(A)) then //3 is the norm of an ideal in the genus of A.
        Append(~LevelList, 3);
        end if;

        if #LevelList eq 0 then
          vprintf HilbertModularForms: "No exceptional HZ divisors found";
          return false;
        end if;

        //Compute intersections of HZ divisors with cusps.
        IntList := [];
        for M in LevelList do
          HZInt := HZCuspIntersection(Gamma, M);
            
          HZIntList := [];
          assert #HZInt eq #res;
          for i in [1 .. #HZInt] do
            for j in [1 .. res[i][4]] do
              HZIntList cat:= HZInt[i];
            end for;
          end for;
          Append(~IntList, HZIntList);
        end for;
        
        //Blow down any subset of the HZ divisors and check if we have a good configuration.
        for I in Subsets({1 .. #LevelList}) do
          if #I eq 0 then //Without blowing down, nothing to do.
            continue;
          else
            // List of indices s.t. boundary curve is now exceptional
            exc_indices := [i : i in [1 .. #self_int_res] |
                            self_int_res[i] + &+[ IntList[j][i] : j in I] eq -1];

            if #exc_indices le 1 then //One (-1)-curve is not enough!
              continue;
            end if;

            // For each two blown down expectional boundary curves, do they intersect?

            for S in Subsets(Set(exc_indices), 2) do
              T := SetToSequence(S);
              for j in I do
                if IntList[j][T[1]] ne 0 and IntList[j][T[2]] ne 0 then
                  vprintf HilbertModularForms: "Blow down curves F_N for N in %o\n", LevelList[SetToSequence(I)];
                  return true;
                end if;
              end for;
            end for;
          end if;

        end for;

    
    else // We consider HZ divisors associated to lambda.
        N := Level(Gamma);
        b := Component(Gamma);

        
//        N := Generator(Level(Gamma) meet Integers());
//        require Norm(Component(Gamma)) eq 1: "Only principal genus supported for higher level.";
//        if N in [1 .. 10] cat [12, 13, 16, 18, 25] then
//        Append(~LevelList, N^2);
//        end if;
    end if;

    return false;
end intrinsic;


intrinsic OldRationalityCriterion(Gamma) -> BoolElt
{Checks whether the Rationality Criterion is satisfied.
 Note 1: Only implemented for Gamma0(N) level.
 Note 2: it could be refined by including more Hirzebruch--Zagier divisors and resolution cycles 
 coming from elliptic points.}

    require GammaType(Gamma) eq "Gamma0": "Only implemented for Gamma0";

    F := BaseField(Gamma);

    //Make a list of intersection numbers of cuspidal resolution cycles.
    res := CuspsWithResolution(Gamma);
    self_int_res := [];
    for x in res do
      for y in [1..x[4]] do
          self_int_res cat:= x[3];
      end for;
    end for;

    LevelList := [];

    //Make a list of possible exceptional Hirzebruch--Zagier divisors.
    if Norm(Level(Gamma)) eq 1 then //vdG VII.4 gives the following
      A := Component(Gamma);
      if Norm(A) eq 1 then
        Append(~LevelList, 1);
        Append(~LevelList, 4);
        Append(~LevelList, 9);
      end if;

      if NormEquation(F, 2*Norm(A)) then //2 is the norm of an ideal in the genus of A.
        Append(~LevelList, 2);
      end if;

      if NormEquation(F, 3*Norm(A)) then //3 is the norm of an ideal in the genus of A.
        Append(~LevelList, 3);
      end if;

    else //for now, only consider F_N if genus(F_N) = 0
      N := Generator(Level(Gamma) meet Integers());
      require Norm(Component(Gamma)) eq 1: "Only principal genus supported for higher level.";
      if N in [1 .. 10] cat [12, 13, 16, 18, 25] then
        Append(~LevelList, N^2);
      end if;
    end if;

    if #LevelList eq 0 then
      vprintf HilbertModularForms: "No exceptional HZ divisors found";
      return false;
    end if;

    //Compute intersections of HZ divisors with cusps.
    IntList := [];
    for M in LevelList do
      HZInt := HZCuspIntersection(Gamma, M);
      HZIntList := [];
      assert #HZInt eq #res;
      for i in [1 .. #HZInt] do
        for j in [1 .. res[i][4]] do
          HZIntList cat:= HZInt[i];
        end for;
      end for;
      Append(~IntList, HZIntList);
    end for;

    //Blow down any subset of the HZ divisors and check if we have a good configuration.
    for I in Subsets({1 .. #LevelList}) do
      if #I eq 0 then //Without blowing down, nothing to do.
        continue;
      else
        // List of indices s.t. boundary curve is now exceptional
        exc_indices := [i : i in [1 .. #self_int_res] |
                        self_int_res[i] + &+[ IntList[j][i] : j in I] eq -1];

        if #exc_indices le 1 then //One (-1)-curve is not enough!
          continue;
        end if;

        // For each two blown down expectional boundary curves, do they intersect?

        for S in Subsets(Set(exc_indices), 2) do
          T := SetToSequence(S);
          for j in I do
            if IntList[j][T[1]] ne 0 and IntList[j][T[2]] ne 0 then
              vprintf HilbertModularForms: "Blow down curves F_N for N in %o\n",
                                           LevelList[SetToSequence(I)];
              return true;
            end if;
          end for;
        end for;
      end if;

    end for;

    return false;
end intrinsic;
