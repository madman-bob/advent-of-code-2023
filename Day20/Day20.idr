import Control.Monad.State
import Data.DPair
import Data.List.Elem
import Data.List.Quantifiers
import Data.String.Parser
import Deriving.Show
import System.File

%default total
%language ElabReflection

setAll : Elem x xs -> p x -> All p xs -> All p xs
setAll Here px (_ :: pxs) = px :: pxs
setAll (There i) px (py :: pxs) = py :: setAll i px pxs

toElem : Any p xs -> Exists (\x => (Elem x xs, p x))
toElem (Here px) = Evidence _ (Here, px)
toElem (There idx) = bimap id (mapFst There) $ toElem idx

data ModuleType = FlipFlop | Conjunction | Broadcast

%hint
showModuleType : Show ModuleType
showModuleType = %runElab derive

record Module where
    constructor MkModule
    moduleType : ModuleType
    name : String
    outputs : List String

%hint
showModule : Show Module
showModule = %runElab derive

record ModuleConfig where
    constructor MkModuleConfig
    modules : List Module
    broadcaster : Elem mBroadcaster modules

findModule : {ms : List Module} ->
             (nm : String) ->
             Maybe (Exists $ \m => (Elem m ms, m.name = nm))
findModule nm = case any (\m => decEq m.name nm) ms of
    Yes idx => Just $ toElem idx
    No _ => Nothing

findModules : {ms : List Module} ->
              List String ->
              List (Exists $ \m => Elem m ms)
findModules nms = do
    nm <- nms
    case findModule nm of
        Just idx => pure $ bimap id fst idx
        Nothing => []

inputs : (config : ModuleConfig) ->
         (nm : String) ->
         List String
inputs config nm = map name $ filter (\m => elem nm m.outputs) config.modules

data ModuleState : ModuleConfig -> Module -> Type where
    MSFF : m.moduleType = FlipFlop =>
           (isOn : Bool) ->
           ModuleState config m
    MSC : m.moduleType = Conjunction =>
          (inputs : All (\n => Dec (Elem m.name n.outputs, Bool)) config.modules) ->
          ModuleState config m
    MSB : m.moduleType = Broadcast =>
          ModuleState config m

record CircuitState (config : ModuleConfig) where
    constructor MkState
    moduleStates : All (ModuleState config) config.modules
    highPulseCount : Nat
    lowPulseCount : Nat
    activated : Bool

S : ModuleConfig -> Type -> Type
S config = State (CircuitState config)

getState : Elem m config.modules -> S config (ModuleState config m)
getState i = gets $ indexAll i . moduleStates

setState : Elem m config.modules -> ModuleState config m -> S config ()
setState i ms = modify {moduleStates $= setAll i ms}

addPulseCount : (isHigh : Bool) -> Nat -> S config ()
addPulseCount False n = modify {lowPulseCount $= (+ n)}
addPulseCount True n = modify {highPulseCount $= (+ n)}

activate : S config ()
activate = modify {activated := True}

initState : {config : ModuleConfig} -> CircuitState config
initState = MkState (initState' config.modules) 0 0 False
  where
    initInputs : (nm : String) ->
                 (ms : List Module) ->
                 All (\n => Dec (Elem nm n.outputs, Bool)) ms
    initInputs nm [] = []
    initInputs nm (m :: ms) = viaEquivalence (MkEquivalence (, False) fst) (isElem nm m.outputs) :: initInputs nm ms

    initModuleState : (m : Module) -> ModuleState config m
    initModuleState m with (m.moduleType) proof p
      _ | FlipFlop = MSFF False
      _ | Conjunction = MSC $ initInputs m.name config.modules
      _ | Broadcast = MSB

    initState' : (ms : List Module) -> All (ModuleState config) ms
    initState' [] = []
    initState' (m :: ms) = initModuleState m :: initState' ms

record Pulse config where
    constructor MkPulse
    from : Elem mFrom config.modules
    to : Elem mTo config.modules
    isHigh : Bool

{config : ModuleConfig} -> Show (Pulse config) where
    show p = do
        let fromName = name $ get config.modules p.from
        let toName = name $ get config.modules p.to
        let strength = if p.isHigh then "high" else "low"
        "\{fromName} -\{strength}-> \{toName}"

initPulse : {config : ModuleConfig} -> Pulse config
initPulse = MkPulse config.broadcaster config.broadcaster False

sendPulse : {config : ModuleConfig} ->
            {default "" activationModule : String} ->
            Pulse config ->
            S config (List (Pulse config))
sendPulse p = do
    let to = get config.modules p.to
    if to.name == activationModule && not p.isHigh
        then activate
        else pure ()
    case !(getState p.to) of
        MSFF isOn => if p.isHigh
            then pure []
            else do
                setState p.to (MSFF $ not isOn)
                addPulseCount (not isOn) $ length $ outputs to
                pure $ map (\(Evidence m output) => MkPulse p.to output $ not isOn) $ findModules $ outputs to
        MSC inputs => do
            let inputs = setAll p.from (viaEquivalence (MkEquivalence (mapSnd $ const p.isHigh) id) $ indexAll p.from inputs) inputs
            let allHigh = all id $ forget $ mapProperty (\case
                      Yes (_, input) => input
                      No _ => True
                  ) inputs
            setState p.to (MSC inputs)
            addPulseCount (not allHigh) $ length $ outputs to
            pure $ map (\(Evidence m output) => MkPulse p.to output $ not allHigh) $ findModules $ outputs to
        MSB => do
            addPulseCount p.isHigh $ length $ outputs to
            pure $ map (\(Evidence m output) => MkPulse p.to output p.isHigh) $ findModules $ outputs to

sendPulses : {config : ModuleConfig} ->
             {default "" activationModule : String} ->
             List (Pulse config) ->
             S config (List (Pulse config))
sendPulses ps = map concat $ traverse (sendPulse {activationModule}) ps

covering
pressButton : {config : ModuleConfig} ->
              {default "" activationModule : String} ->
              CircuitState config ->
              CircuitState config
pressButton startState = execState ({lowPulseCount $= S} startState) $ propagate [initPulse]
  where
    propagate : List (Pulse config) -> S config ()
    propagate [] = pure ()
    propagate ps = sendPulses {activationModule} ps >>= propagate

covering
pressButtonN : (config : ModuleConfig) ->
               {default initState cs : CircuitState config} ->
               Nat ->
               Nat
pressButtonN config 0 = highPulseCount cs * lowPulseCount cs
pressButtonN config (S n) = pressButtonN config {cs = pressButton cs} n

covering
pressTillOn : (config : ModuleConfig) ->
              {default initState cs : CircuitState config} ->
              {default 0 start : Nat} ->
              (activationModule : String) ->
              Nat
pressTillOn config activationModule = if cs.activated
    then start
    else pressTillOn config {cs = pressButton {activationModule} cs} {start = S start} activationModule

covering
name : Parser String
name = map pack $ some letter

covering
names : Parser (List String)
names = many (name <* optional (string ", "))

covering
module_ : Parser Module
module_ = [| MkModule
    ((char '%' *> pure FlipFlop) <|> (char '&' *> pure Conjunction) <|> (pure Broadcast))
    (lexeme name <* token "->")
    names
  |]

covering
moduleConfig : Parser ModuleConfig
moduleConfig = do
    modules <- many (lexeme module_)
    let Just (Evidence _ (idx, _)) = findModule "broadcaster"
        | Nothing => fail "No broadcast module found"
    eos
    pure $ MkModuleConfig modules idx

covering
main : IO ()
main = do
    let eg1 = """
    broadcaster -> a, b, c
    %a -> b
    %b -> c
    %c -> inv
    &inv -> a
    """

    let Right (eg1, _) = parse moduleConfig eg1
        | Left err => putStrLn err

    let eg2 = """
    broadcaster -> a
    %a -> inv, con
    &inv -> b
    %b -> con
    &con -> output
    """

    let Right (eg2, _) = parse moduleConfig eg2
        | Left err => putStrLn err

    Right input <- readFile "Day20/input"
            | Left err => printLn err

    let Right (input, _) = parse moduleConfig input
            | Left err => putStrLn err

    putStrLn "Part 1"
    printLn $ pressButtonN eg1 1000
    printLn $ pressButtonN eg2 1000
    printLn $ pressButtonN input 1000

    putStrLn "Part 2"
    -- Another question with unstated assumptions
    -- Attempting to solve the question written will take too long
    -- There are four independent sub-circuits, and the whole circuit will activate when the sub-circuits activate simultaneously.
    -- So the solution is the LCM of the following
    let subcircuits = inputs input "rx" >>= inputs input
    printLn $ map (pressTillOn input) subcircuits
