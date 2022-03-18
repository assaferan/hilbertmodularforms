freeze;

// Copied from ModFrmHil/hackobj.m and modified

/**********************************************************************
  ModFrmHil attributes
  Let M be a ModFrmHil over the FldNum F    
**********************************************************************/

declare type ModFrmHil [ModFrmHilElt];

declare attributes ModFrmHil :  

  Field,                     // = F = BaseField(M), required to be an absolute field (for efficiency)
  Level,                     // = Level(M) = an ideal in Integers(F)
  DirichletCharacter,        // always assigned: either the integer 1, or a GrpDrchNFElt with modulus Level(M)

  Weight,                    // = Weight(M) = a sequence of integers, corresponding to InfinitePlaces(F)
  CentralCharacter,          // Only used internally.

  NewLevel,                  // = NewLevel(M). M is the space of forms that are new at this level or higher
                             // (See intrinsic NewSubspace(M,I).  Must be assigned on creation)
  Dimension,                 

  QuaternionOrder,           // An order in a quaternion algebra (type AlgAssVOrd or AlgQuatOrd)
                             // If definite, should be maximal, and Dembele's algorithm will be used.
                             // If indefinite, the Greenberg-Voight implementation will be used.

  force_indefinite,          // Secret, not for public use

  Ambient,                   // This is a larger space on which Hecke operators are computed and stored.
                             // Hecke operators on M are obtained from those via M`basis_matrix_wrt_ambient.
                             // If not assigned but QuaternionOrder is assigned, M is its own ambient.
                             // If neither are assigned, we haven't yet decided how to compute M.

  //////  BASIS MATRICES  /////

  basis_matrix,              // The rows generate M inside the vector space V used to compute it 
  basis_matrix_inv,          // basis_matrix * basis_matrix_inv = identity
  basis_is_honest,           // IMPORTANT CONVENTION:
                             // Let B = basis_matrix.  
                             // The rowspace of B defines an image of M in some larger space.   
                             // This subspace is not required to actually be Hecke-invariant.  
                             // We only need that B maps isomorphically to V/C, where C is a  
                             // Hecke-invariant complement. 
                             // Bi = basis_matrix_inv is uniquely determined from B and C, by
                             //   B * Bi = identity
                             //   C * Bi = zero
                             // Therefore we obtain the Hecke action on V/C (wrt some basis) as
                             //   T = B * T_V * Bi 
                             
                             // Definition: we will say B is an "honest" basis_matrix if its 
                             // rowspace is a Hecke-invariant subspace.

                             // When B *is* honest, we do not require the second condition 
                             //   C * Bi = zero

                             // The reason for this convention is that in many situations, we know 
                             // the Hecke-invariant space C but not a Hecke-invariant complement B;  
                             // To compute honest B from C is expensive in general, by any method.

  basis_matrix_wrt_ambient,  // basis_matrix_wrt_ambient * Ambient`basis_matrix = basis_matrix
  basis_matrix_wrt_ambient_inv, // basis_matrix_wrt_ambient * basis_matrix_wrt_ambient_inv = identity
                             // The same convention as for basis_matrix must be observed.  
                             // These matrices must have BaseRing = hecke_matrix_field(Ambient(M))

  basis_matrix_big,          // The raw space in the definite case (see HilbertModularSpaceBasisMatrix).
  basis_matrix_big_inv,      // (It's an "honest" basis matrix: the space is invariant under the Hecke action)
  eisenstein_basis,

  InnerProduct,
  InnerProductBig,

  /////  HECKE MATRICES   /////

  Hecke,                     // Arrays indexed by primes p of Integers(F) 
  HeckeCharPoly,             //(initialized on creation)
  HeckeBig,
  HeckeBigColumns,           // Used in HeckeOperatorDefiniteBig

  AL,                        // Arrays indexed by primes dividing Level(M),
  DegDown1,                  // storing AtkinLehner and degeneracy operators
  DegDownp,
  ALBig,
  DegDown1Big,
  DegUp1Big,
  DegUppBig,

  // hack begins
  Diamond,                   // Arrays indexed by ideals representing the class group of Integers(F)
  // hack ends

  hecke_matrix_field,        // The Hecke operators are matrices with entries in this field.
                             // Automatically assigned to be Q for parallel weight 2.
  hecke_matrix_field_is_minimal, // true iff hecke_matrix_field is the natural field (must be assigned).

  hecke_algebra,             // stores result of function hecke_algebra (this could change)
  hecke_algebra_generator,
  hecke_algebra_generator_eigenvalue,
  
  /////  NEW SUBSPACES   //////

  is_cuspidal,               // always true, currently (and must be initialized on creation)

  is_new,                    // true for spaces with NewLevel = Level

  FullSpace,                 // For a NewSubspace, this is the associated space with NewLevel = (1)
                             // DO NOT confuse with Ambient!

  NewSubspaces,              // List of tuples <I, MI> where MI is the space of NewLevel = I
                             // (this should be stored on the associated FullSpace)

  //////  EIGENSPACES   ///////

  HeckeMethod,               // [temp] method used in NewformDecomposition and Eigenform

  NewformDecomposition,      // = NewformDecomposition(M)
  NewSpace,                  // [temp?] the space whose NewformDecompostion this space is in

  HeckeIrreducible,          // True for spaces in the NewformDecomposition of a new space

  Eigenform,                 // = Eigenform(M), valid when HeckeIrreducible is true

  /////  STUFF FOR THE DEFINITE CASE 

  rids,                      // Sequence of right ideal class reps for M`QuaternionOrder, chosen and 
                             // ordered once and for all -- SHOULD ONLY BE ACCESSED VIA 'get_rids'.

  splitting_map,             // Homomorphism from QuaternionOrder(M) to 2x2 matrices over the residue ring 
                             // Integers(F)/d where d = Level(M)/Discriminant(Algebra(QuaternionOrder(M)))

  ModFrmHilDirFacts,         // Sequence of records of format ModFrmHilDirFact (defined in definite.m)

  weight_rep,                // The weight representation: B^* -> GL_2(K)^g -> GL(V_k).

  weight_dimension,          // The dimension of the weight space.

  weight_base_field;         // The base field of the weight representation,
                             // or Rationals() for parallel weight 2
