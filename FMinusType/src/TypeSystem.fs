namespace FMinus

open AST
// Type.infer() must raise this if the input program seems to have a type error.
exception TypeError
// The types available in our F- language.
type Type =
    | Int
    | Bool
    | TyVar of string
    | Func of Type * Type

type TypeEnv = Map<string, Type>
type SubsEnv = Map<Type, Type>
type Equation = (Type * Type)

module Type =
    let mutable counter = 0
    let mutable eqNeqList = []
    let mutable varMap = Map.empty<Exp, Type>

    let typeVarMaker () =
        counter <- counter + 1
        TyVar(sprintf "mjtv%d" counter) //새로운 변수, 절대 겹치지 않게끔
    // Convert the given 'Type' to a string.
    let rec toString (typ: Type) : string =
        match typ with
        | Int -> "int"
        | Bool -> "bool"
        | TyVar s -> s
        | Func(t1, t2) -> sprintf "(%s) -> (%s)" (toString t1) (toString t2)

    let rec Gen (env: TypeEnv) (exp: Exp) (t: Type) : Equation list = //(좌변 = 우변) 을 원소로 하는 리스트.
        match exp with
        | Num _ -> [ (t, Int) ]
        | True
        | False -> [ (t, Bool) ]
        | Var x ->
            match Map.tryFind x env with
            | Some ty -> [ (t, ty) ]
            | None ->
                match Map.tryFind (Var x) varMap with
                | Some ty2 -> [ (t, ty2) ]
                | None ->
                    let newtv1 = typeVarMaker ()
                    let _ = varMap <- Map.add (Var x) newtv1 varMap
                    [ (t, newtv1) ]
        | Neg e1 -> [ (t, Int) ] @ Gen env e1 Int
        | Add(e1, e2)
        | Sub(e1, e2) -> [ (t, Int) ] @ Gen env e1 Int @ Gen env e2 Int
        | LessThan(e1, e2)
        | GreaterThan(e1, e2) -> [ (t, Bool) ] @ Gen env e1 Int @ Gen env e2 Int
        | IfThenElse(e1, e2, e3) -> Gen env e1 Bool @ Gen env e2 t @ Gen env e3 t
        | LetIn(str, e1, e2) ->
            let newtv1 = typeVarMaker ()
            let newenv = Map.add str newtv1 env
            Gen env e1 newtv1 @ Gen newenv e2 t
        | LetFunIn(str1, str2, e1, e2) ->
            let newtvarg = typeVarMaker ()
            let newtvret = typeVarMaker ()
            let newenvarg = Map.add str2 newtvarg env
            let newenvfunc = Map.add str1 (Func(newtvarg, newtvret)) env
            Gen newenvarg e1 newtvret @ Gen newenvfunc e2 t
        | LetRecIn(str1, str2, e1, e2) ->
            let newtvarg = typeVarMaker ()
            let newtvret = typeVarMaker ()
            let newenvfunc = Map.add str1 (Func(newtvarg, newtvret)) env
            let newenvarg = Map.add str2 newtvarg newenvfunc
            //I lost points on my assignment because of this small mistake - I had "Gen newenvarg e1 newtvarg" instead of  "Gen newenvarg e1 newtvret" in the code. I've fixed it now, though. It was such a silly error!
            Gen newenvarg e1 newtvret @ Gen newenvfunc e2 t
        | Fun(str, e1) ->
            let newtvarg = typeVarMaker ()
            let newtvret = typeVarMaker ()
            // printfn "!!  %A %A %A" t newtvarg newtvret
            let newenv = Map.add str newtvarg env
            [ (t, Func(newtvarg, newtvret)) ] @ Gen newenv e1 newtvret
        | App(e1, e2) ->
            let newtv1 = typeVarMaker ()
            Gen env e1 (Func(newtv1, t)) @ Gen env e2 newtv1
        | Equal(e1, e2)
        | NotEq(e1, e2) -> //두 타입이 뭔지는 모르겠지만 겨로가는 Bool이어야하고, 둘이 서로 같아야한다.
            let newtv1 = typeVarMaker ()
            let newtv2 = typeVarMaker ()
            eqNeqList <- newtv1 :: eqNeqList
            Gen env e1 newtv1 @ Gen env e2 newtv2 @ [ (t, Bool) ] @ [ (newtv1, newtv2) ]
    // Return the inferred type of the input program.
    and Apply (subs: SubsEnv) (t: Type) : Type =
        match t with
        | Int
        | Bool -> t
        | TyVar tau ->
            match Map.tryFind (TyVar tau) subs with
            | Some ty -> ty
            | None -> TyVar tau
        | Func(ty1, ty2) -> Func((Apply subs ty1), (Apply subs ty2))

    // and Unify (eq: Equation) (subs: SubsEnv) : SubsEnv =
    //     match eq with
    //     | (t1, t2) -> Extend ((Apply subs t1), (Apply subs t2)) subs

    // and findTauT (tau) (t: Type) value : Type = //Map.map 위해서 만듦. 맵에서 타우 찾아서 티로 다 바꾸게끔, Func안에도
    //     match value with
    //     | TyVar tv1 -> if tau = tv1 then t else value
    //     | Func(ty1, ty2) -> Func(findTauT tau t ty1, findTauT tau t ty2)
    //     | _ -> value

    // and Extend (eq: Equation) (subs: SubsEnv) : SubsEnv =
    //     match eq with
    //     | (Int, Int)
    //     | (Bool, Bool) -> subs
    //     | (Func(arg1, ret1), Func(arg2, ret2)) -> Unify (ret1, ret2) (Extend (arg1, arg2) subs)
    //     | (TyVar tau, t)
    //     | (t, TyVar tau) ->
    //         if checkInfLoop (TyVar tau, t) then
    //             raise TypeError
    //         elif TyVar tau = t then
    //             subs
    //         else
    //             let nextSubs = Map.map (fun k v -> findTauT tau t v) subs
    //             Map.add (TyVar tau) t nextSubs
    //     | _ -> raise TypeError
    and Unify (eq: Equation) (subs: SubsEnv) : SubsEnv =
        match eq with
        | (t1, t2) -> Extend ((Apply subs t1), (Apply subs t2)) subs

    and findTauT (tau) (t: Type) value : Type =
        match value with
        | TyVar tv1 -> if tau = tv1 then t else value
        | Func(ty1, ty2) -> Func(findTauT tau t ty1, findTauT tau t ty2)
        | _ -> value

    and Extend (eq: Equation) (subs: SubsEnv) : SubsEnv =
        match eq with
        | (Int, Int)
        | (Bool, Bool) -> subs
        | (Func(arg1, ret1), Func(arg2, ret2)) -> Unify (ret1, ret2) (Extend (arg1, arg2) subs)
        | (TyVar tau, t) ->
            if checkInfLoop (TyVar tau, t) then
                raise TypeError
            elif TyVar tau = t then
                subs
            elif t = Int || t = Bool then // 즉시 치환
                let nextSubs = Map.map (fun k v -> findTauT tau t v) subs
                Map.add (TyVar tau) t nextSubs
            else
                let nextSubs = Map.map (fun k v -> findTauT tau t v) subs
                Map.add (TyVar tau) t nextSubs
        | (t, TyVar tau) ->
            if checkInfLoop (TyVar tau, t) then
                raise TypeError
            elif TyVar tau = t then
                subs
            else
                let nextSubs = Map.map (fun k v -> findTauT tau t v) subs
                Map.add (TyVar tau) t nextSubs
        | _ -> raise TypeError

    and checkInfLoop (eq: Equation) : bool = //루프 돌아가면 안되니까 쳌 //순환참조 하는지 체크해야함.
        match eq with
        | ty1, Func(arg, ret) ->
            if (ty1 = arg) || (ty1 = ret) then
                true
            else
                checkInfLoop (ty1, arg) || checkInfLoop (ty1, ret)
        | _ -> false

    and goCheck (eqlist: Equation list) (subs: SubsEnv) : SubsEnv = // eq 를 subs 다 쫘르륵합쳐주기
        match eqlist with
        | head :: tail ->
            let nextSubs = Unify head subs //만들어진 EQ list를  Unify를 사용해서 fold
            goCheck tail nextSubs
        | [] -> subs

    // and testType (t: Type) : bool = //Map (Tree) 순회하며 아직 Int나 Bool로 못변한놈들 있으면 바로 raise
    //     match t with
    //     | Int
    //     | Bool -> true
    //     | TyVar v -> raise TypeError
    //     | Func(ty1, ty2) -> testType (ty1) && testType (ty2)

    and testEqNeq (tv) (subs: SubsEnv) : bool =
        match Map.tryFind tv subs with
        | Some i ->
            match i with
            | Int
            | Bool -> true
            | _ -> raise TypeError
        | None -> raise TypeError

    and infer (prog: Program) : Type =
        let inittypevar = typeVarMaker () //tau progarm
        let eqlist = Gen (Map.empty<string, Type>) prog inittypevar //방정식 만들기
        let finalSubs = goCheck eqlist Map.empty<Type, Type> // 연립하기
        // let _ = Map.filter (fun _ value -> testType value) finalSubs // tree완성 안된거 있는지 확인하기 -> 있으면 바로 raise
        let _ = List.filter (fun tv -> testEqNeq tv finalSubs) eqNeqList //eq나 noteq에 들어갓던 변수중에 최종 매핑이 int나 bool이 아닌놈 있으면 raise

        match Map.tryFind inittypevar finalSubs with //tau program 값 출력
        | Some i -> i
        | None -> raise TypeError
// namespace FMinus

// open AST

// // Type.infer() must raise this if the input program seems to have a type error.
// exception TypeError

// // The types available in our F- language.
// type Type =
//     | Int
//     | Bool
//     | TyVar of string
//     | Func of Type * Type

// type TypeEnv = Map<string, Type>
// type TypeEquation = (Type * Type) list
// type Substitute = (string * Type) list

// module Type =

//     let mutable equaltyVarlist = []
//     let mutable tyVarNum = 0
//     // Convert the given 'Type' to a string.
//     let rec toString (typ: Type) : string =
//         match typ with
//         | Int -> "int"
//         | Bool -> "bool"
//         | TyVar s -> s
//         | Func(t1, t2) -> sprintf "(%s) -> (%s)" (toString t1) (toString t2)

//     let rec tyVar_naming () : string =
//         let name = sprintf "t%d" tyVarNum
//         tyVarNum <- tyVarNum + 1
//         name

//     let rec occur_check (t1: Type) (t2: Type) : bool = //occurs check
//         match t2 with
//         | Int -> false
//         | Bool -> false
//         | TyVar s -> s = (toString t1)
//         | Func(tx, ty) -> occur_check t1 tx || occur_check t1 ty

//     let rec gen (env: TypeEnv) (e: Exp) (t: Type) : TypeEquation =
//         match e with
//         | Num _ -> [ (t, Int) ]
//         | True
//         | False -> [ (t, Bool) ]
//         | Var x ->
//             match Map.tryFind x env with
//             | Some t1 -> [ (t, t1) ]
//             | None -> raise TypeError
//         | Neg e1 -> gen env e1 t
//         | Add(e1, e2)
//         | Sub(e1, e2) -> [ (t, Int) ] @ (gen env e1 Int) @ (gen env e2 Int)
//         | LessThan(e1, e2)
//         | GreaterThan(e1, e2) -> [ (t, Bool) ] @ (gen env e1 Int) @ (gen env e2 Int)
//         | Equal(e1, e2)
//         | NotEq(e1, e2) ->
//             let (t1, t2) = (TyVar(tyVar_naming ()), TyVar(tyVar_naming ()))
//             equaltyVarlist <- equaltyVarlist @ [ (toString t1, toString t2) ]
//             [ (t, Bool) ] @ [ (t1, t2) ] @ (gen env e1 t1) @ (gen env e2 t2)
//         | IfThenElse(e1, e2, e3) -> (gen env e1 Bool) @ (gen env e2 t) @ (gen env e3 t)
//         | LetIn(x, e1, e2) ->
//             let t1 = TyVar(tyVar_naming ())
//             (gen env e1 t1) @ (gen (Map.add x t1 env) e2 t)
//         | LetFunIn(f, x, e1, e2) ->
//             let (t_arg, t_res) = (TyVar(tyVar_naming ()), TyVar(tyVar_naming ()))

//             (gen (Map.add x t_arg env) e1 t_res)
//             @ (gen (Map.add f (Func(t_arg, t_res)) env) e2 t)
//         | LetRecIn(f, x: string, e1, e2) ->
//             let (t_arg, t_res) = (TyVar(tyVar_naming ()), TyVar(tyVar_naming ()))
//             let _env = gen (Map.add f (Func(t_arg, t_res)) (Map.add x t_arg env)) e1 t_res
//             let __env = (gen (Map.add f (Func(t_arg, t_res)) env) e2 t)
//             _env @ __env
//         | Fun(x, e) ->
//             let (t_arg, t_res) = (TyVar(tyVar_naming ()), TyVar(tyVar_naming ()))
//             [ (t, Func(t_arg, t_res)) ] @ (gen (Map.add x t_arg env) e t_res)
//         | App(e1, e2) ->
//             let t_arg = TyVar(tyVar_naming ())
//             (gen env e1 (Func(t_arg, t))) @ (gen env e2 t_arg)

//     let rec application (s: Substitute) (t: Type) : Type =
//         match t with
//         | Int -> Int
//         | Bool -> Bool
//         | TyVar k ->
//             match List.tryFind (fun (x, y) -> x = k) s with
//             | Some(_, t) -> t
//             | None -> TyVar k
//         | Func(t1, t2) -> Func(application s t1, application s t2)

//     let merge (tx: string) (ty: Type) (s: Substitute) =
//         //(tx, ty)::(List.map (fun (x, y) -> (toString (application [(tx, ty)] (TyVar x)), application [(tx, ty)] y)) s)
//         (tx, ty) :: (List.map (fun (x, y) -> (x, application [ (tx, ty) ] y)) s)

//     let rec unify (t1: Type) (t2: Type) (s: Substitute) : Substitute =
//         let rec extend (t1: Type) (t2: Type) (s: Substitute) : Substitute =
//             // printfn "t1: %A, t2: %A" t1 t2

//             match (t1, t2) with
//             | (Int, Int)
//             | (Bool, Bool) -> s
//             | (TyVar x, _) ->
//                 match t2 with
//                 | TyVar y -> if x = y then s else merge x t2 s
//                 | _ ->
//                     if occur_check (TyVar x) t2 then
//                         raise TypeError
//                     else
//                         merge x t2 s
//             | (_, TyVar t) -> extend (TyVar t) t1 s
//             | (Func(tx1, ty1), Func(tx2, ty2)) ->
//                 let _s = extend tx1 tx2 s
//                 // printfn "_s: %A" _s
//                 unify ty1 ty2 _s
//             | _ -> raise TypeError

//         extend (application s t1) (application s t2) s

//     let rec solve (typeEquation: TypeEquation) (s: Substitute) : Substitute =
//         let rec solve_inner (typeEquation: TypeEquation) (s: Substitute) : Substitute =
//             // printfn "s: %A" s

//             match typeEquation with
//             | [] -> s
//             | (t1, t2) :: remain ->
//                 let _s = unify t1 t2 s
//                 solve_inner remain _s

//         solve_inner typeEquation s

//     let rec equalvar_check (s: Substitute) : bool =
//         match equaltyVarlist with
//         | [] -> true
//         | (t1, t2) :: remain ->
//             let (t1_tuple, t2_tuple) =
//                 (List.tryFind (fun (x, y) -> x = t1) s, List.tryFind (fun (x, y) -> x = t2) s)

//             match (t1_tuple, t2_tuple) with
//             | Some(x, Int), Some(y, Int)
//             | Some(x, Bool), Some(y, Bool) ->
//                 equaltyVarlist <- remain
//                 equalvar_check s
//             | _ -> false

//     // Return the inferred type of the input program.
//     let infer (prog: Program) : Type =
//         let typeEquation = gen Map.empty prog (TyVar "tp")
//         // printfn "Type Equation: %A" typeEquation
//         let s = solve typeEquation []

//         if (equalvar_check s) then
//             match List.tryFind (fun (x, y) -> x = "tp") s with
//             | Some(_, t) -> t
//             | None -> raise TypeError
//         else
//             raise TypeError
