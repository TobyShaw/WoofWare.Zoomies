namespace WoofWare.Zoomies

open System.Runtime.CompilerServices
open TypeEquality
open WoofWare.Incremental
open System.Collections.Generic

type Effect = unit -> unit

module Effect =

    let empty: Effect = ignore

type Environment =
    { results: Dictionary<TypeIdCrate, NodeCrate>
      incremental: Incremental
      effectsToRun : Queue<Effect>
    }

module Teq =
    module Cong =
        let node (teq: Teq<'a, 'b>) : Teq<Node<'a>, Node<'b>> = Teq.Cong.believeMe teq

module Environment =

    let empty =
        { results = Dictionary()
          incremental = Incremental.make ()
          effectsToRun = Queue() }

    let add typeId result environment =
        match environment.results.TryAdd(TypeIdCrate.make typeId, NodeCrate.make result) with
        | true -> Ok()
        | false -> Error $"%A{typeId} already exists in environment"

    let get (typeId: TypeId<'a>) environment =
        match environment.results.TryGetValue(TypeIdCrate.make typeId) with
        | true, resultCrate ->
            resultCrate.Apply
                { new NodeEval<_> with
                    member _.Eval arg = Some(unbox<Node<'a>> arg) }
        | false, _ -> None

[<IsByRefLike; Struct>]
type Graph =
    { generator: TypeIdGenerator
      mapper: ComputationMapper ref }

and ComputationMapper =
    abstract Run: 'a Bonsai Trampoline -> 'a Bonsai Trampoline

and Sub<'args, 'a> =
    abstract Run: Graph * 'args -> 'a

and 'a Bonsai =
    | Return of 'a
    | Incremental of 'a Node
    | Apply of ApplyCrate<'a>
    | Switch of Bonsai<int> * Sub<int, 'a Bonsai>
    | State of StateCrate<'a>
    | Let of LetCrate<'a>
    | Var of TypeId<'a>

and ApplyCrate<'a> =
    abstract Apply<'ret> : ApplyEval<'a, 'ret> -> 'ret

and ApplyEval<'a, 'ret> =
    abstract Eval<'b> : Bonsai<'b> -> Bonsai<'b -> 'a> -> 'ret

and StateCrate<'a> =
    abstract Apply<'ret> : StateEval<'a, 'ret> -> 'ret

and StateEval<'a, 'ret> =
    abstract Eval<'model, 'update> :
        initial: 'model * update: ('model -> 'update -> 'model) * Teq<'a, 'model * ('update -> Effect)> -> 'ret

and LetCrate<'a> =
    abstract Apply<'ret> : LetEval<'a, 'ret> -> 'ret

and LetEval<'a, 'ret> =
    abstract Eval<'inner> : from: Bonsai<'inner> * via: TypeId<'inner> * Bonsai<'a> -> 'ret


module Driver =

    let rec eval<'a> (env: Environment) : Bonsai<'a> -> Node<'a> =
        function
        | Return x -> env.incremental.Return x
        | Incremental node -> node
        | Apply applyCrate ->
            applyCrate.Apply
                { new ApplyEval<_, _> with
                    member this.Eval x f =
                        let x = eval env x
                        let f = eval env f
                        env.incremental.Map2 (fun f x -> f x) f x }
        | Let letCrate ->
            letCrate.Apply
                { new LetEval<_, _> with
                    member _.Eval(from, via, into) =
                        let from = eval env from

                        match env |> Environment.add via from with
                        | Ok() -> eval env into
                        | Error s -> failwith s }
        | Var typeId ->
            match env |> Environment.get typeId with
            | Some result -> result
            | None -> failwith $"%A{typeId} does not exist in environment"

        | State stateCrate ->
            stateCrate.Apply
                { new StateEval<_, _> with
                    member _.Eval(initial: 'model, update: 'model -> 'update -> 'model, teq) =
                        let model = env.incremental.Var.Create initial
                        let triggerUpdate update = fun () -> env.incremental.Var.Set model (update envi

                        let result: ('model * ('update -> Effect)) Node = failwith ""

                        result |> Teq.castFrom (Teq.Cong.node teq)

                }
        | _ -> failwith "TODO"





type Inputs = { EnterPressed: bool }

module Bonsai =

    let return_ x = Return x

    let apply x f =
        Apply
            { new ApplyCrate<_> with
                member _.Apply eval = eval.Eval x f }

    [<Sealed>]
    type Builder() =
        member this.MergeSources(a, b) =
            return_ (fun a b -> a, b) |> apply a |> apply b

        member this.Return a = return_ a
        member this.BindReturn(x, f) = return_ f |> apply x


    let memo graph name (computationToPerform: 'a Bonsai) =
        let typeId = TypeIdGenerator.generate graph.generator name
        let oldF = !graph.mapper

        let newF =
            { new ComputationMapper with
                member _.Run computation =
                    let newF eventualResult =
                        let let_ =
                            Trampoline.lift (
                                Let
                                    { new LetCrate<_> with
                                        member _.Apply eval =
                                            eval.Eval(computationToPerform, typeId, eventualResult) }
                            )

                        oldF.Run let_

                    trampoline {
                        let! computation = computation
                        return! newF computation
                    } }

        graph.mapper := newF
        Var typeId

    let map f x = return_ f |> apply x

    let unzip b = b |> map fst, b |> map snd

    let if_ (b: Bonsai<bool>) (graph: Graph) (f: Sub<bool, Bonsai<'a>>) : Bonsai<'a> =
        let int =
            b
            |> map (function
                | false -> 0
                | true -> 1)

        memo
            graph
            "if_"
            (Switch(
                int,
                { new Sub<_, _> with
                    member _.Run(graph, int) =
                        match int with
                        | 0 -> f.Run(graph, false)
                        | 1 -> f.Run(graph, true)
                        | _ -> failwith "Impossible" }
            ))

    let state_machine initial update (graph: Graph) =
        let state =
            memo
                graph
                "state_machine"
                (State
                    { new StateCrate<_> with
                        member _.Apply eval = eval.Eval(initial, update, Teq.refl) })

        unzip state

    let state initial (graph: Graph) =
        state_machine initial (fun _prev new_ -> new_) graph

    let edge (input: Bonsai<'a>) (graph: Graph) (callback: Bonsai<'a -> 'a -> Effect>) : unit = failwith "TODO"

[<AutoOpen>]
module Bonsai_open =
    let bonsai = Bonsai.Builder()

module Example =
    let main (inputs: Bonsai<Inputs>) (graph: Graph) : Bonsai<Vdom> =
        let show_panel, set_show_panel = Bonsai.state false graph

        Bonsai.edge
            inputs
            graph
            (bonsai {
                let! set_show_panel = set_show_panel
                and! show_panel = show_panel

                return
                    fun prev curr ->
                        if curr.EnterPressed && not prev.EnterPressed then
                            set_show_panel (not show_panel)
                        else
                            Effect.empty


            })

        let top_two =
            let left =
                bonsai {
                    let! show_panel = show_panel

                    return
                        Vdom.panelSplit
                            Vertical
                            0.8
                            (Vdom.textContent "Left content")
                            (Vdom.labelledCheckbox "Show bottom panel" show_panel)
                }

            let right = Vdom.textContent "Right content"

            bonsai {
                let! left = left
                return Vdom.panelSplit Horizontal 0.5 left right
            }

        Bonsai.if_
            show_panel
            graph
            { new Sub<_, _> with
                member _.Run(graph, b) =
                    match b with
                    | false -> top_two
                    | true ->
                        bonsai {
                            let! top_two = top_two
                            let bottom_panel = Vdom.textContent "Bottom panel"
                            return Vdom.panelSplit Vertical 0.8 top_two bottom_panel
                        } }



// graph : forall a. 'a Computation -> 'a Computation
// Proc === Computation
// Computation = | Return | Leaf0 (state_machine) | Sub | Assoc | Switch | WithModelResetter
//
// Bonsai  === Value
// Value = | Incr | Return | Both | Cutoff | Named ()
//
// perform : graph -> Computation -> Value
//   Value returned is almost always "Named", which looks up in a
