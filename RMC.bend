#### Utility Functions ####

type Maybe:
  None
  Some {val}

Maybe/map f (Maybe/None) = Maybe/None
Maybe/map f (Maybe/Some x) = (Maybe/Some (f x))

# Returns value from a maybe map, along with the map with the value dropped
# Value stored in maybe type
Map/get_drop_maybe map key =
  match map {
    Map/Leaf: (Maybe/None, map)
    Map/Node:
      switch _ = (== 0 key) {
        0: switch _ = (% key 2) {
          0:
            let (got, rest) = (Map/get_drop_maybe map.left (/ key 2))
            (got, (Map/Node map.value rest map.right))
          _:
            let (got, rest) = (Map/get_drop_maybe map.right (/ key 2))
            (got, (Map/Node map.value map.left rest))
        }
        _: (map.value, (Map/Node Maybe/None map.left map.right))
      }
  }

# Map/set but unassigned values are None instead of *
Map/set_maybe map key value =
  match map {
    Map/Node:
      switch _ = (== 0 key) {
        0: switch _ = (% key 2) {
          0: (Map/Node map.value (Map/set_maybe map.left (/ key 2) value) map.right)
          _: (Map/Node map.value map.left (Map/set_maybe map.right (/ key 2) value))
        }
        _: (Map/Node (Maybe/Some value) map.left map.right)
      }
    Map/Leaf:
      switch _ = (== 0 key) {
        0: switch _ = (% key 2) {
          0: (Map/Node Maybe/None (Map/set_maybe Map/Leaf (/ key 2) value) Map/Leaf)
          _: (Map/Node Maybe/None Map/Leaf (Map/set_maybe Map/Leaf (/ key 2) value))
        }
        _: (Map/Node (Maybe/Some value) Map/Leaf Map/Leaf)
      }
  }
  
# Given a maybe map of stacks, try popping off an element.
Map/pop_stack_maybe map key =
  match map {
    Map/Leaf: (Maybe/None, map)
    Map/Node:
      switch _ = (== 0 key) {
        0: switch _ = (% key 2) {
          0:
            let (got, rest) = (Map/pop_stack_maybe map.left (/ key 2))
            (got, (Map/Node map.value rest map.right))
          _:
            let (got, rest) = (Map/pop_stack_maybe map.right (/ key 2))
            (got, (Map/Node map.value map.left rest))
        }
        _: 
          match map.value {
            Maybe/None: ((Maybe/None), (Map/Node Maybe/None map.left map.right))
            Maybe/Some: 
              match map.value.val {
                List/Nil: ((Maybe/None), (Map/Node Maybe/None map.left map.right))
                List/Cons: ((Maybe/Some map.value.val.head), (Map/Node (Maybe/Some map.value.val.tail) map.left map.right))
              }
          }
      }
  }


# Map/map with a default, over a maybe map.
# Note that f will be applied to default when not found.
Map/map_def_maybe map key f default =
  match map {
    Map/Node:
      switch _ = (== 0 key) {
        0: switch _ = (% key 2) {
          0: (Map/Node map.value (Map/map_def_maybe map.left (/ key 2) f default) map.right)
          _: (Map/Node map.value map.left (Map/map_def_maybe map.right (/ key 2) f default))
        }
        _: (Map/Node (Maybe/map f map.value) map.left map.right)
      }
    Map/Leaf:
      switch _ = (== 0 key) {
        0: switch _ = (% key 2) {
          0: (Map/Node Maybe/None (Map/map_def_maybe Map/Leaf (/ key 2) f default) Map/Leaf)
          _: (Map/Node Maybe/None Map/Leaf (Map/map_def_maybe Map/Leaf (/ key 2) f default))
        }
        _: (Map/Node (Maybe/Some (f default)) Map/Leaf Map/Leaf)
      }
  }

Map/map_maybe map f = (Map/map (Maybe/map f) map)

# Why isn't this a built-in?
List/map f (List/Nil) = List/Nil
List/map f (List/Cons x xs) = (List/Cons (f x) (List/map f xs))

String/concat "" st = st
String/concat (String/Cons x xs) st = (String/Cons x (String/concat xs st))


#### Core Implementation ####
# Terms are elements from a term algebra with possible unification variables, a la prolog.
type Term:
  # Variables should consist, generally, of a name (used for dictionary lookup)
  # And a value which will start off as an unscoped lambda variable, but will be
  # a true value if this variable is ever subject to unification.
  Var {name, ~val}
  # Just a wrapper around a string
  Const {str}
  # Args should be a list of Terms (is there a way to get this to work with `fold`, etc?)
  Fun {str, args}

# Render Term as a string
def TermString(trm):
  match trm:
    case Term/Var:
      return String/concat("X$", String/Cons(trm.name + 71, String/Cons('|', TermString(trm.val))))
    case Term/Const:
      return String/Cons(trm.str + 71, String/Nil)
    case Term/Fun:
      return String/Cons(trm.str + 71, String/Cons('(', String/concat(TermArgsString(trm.args), ")")))



def TermArgsString(args):
  match args:
    case List/Nil:
      return ""
    case List/Cons:
      match args.tail:
        case List/Nil:
          return TermString(args.head)
        case List/Cons:
          return String/concat(
                  TermString(args.head), 
                  String/concat(", ", TermArgsString(List/Cons(args.tail.head, args.tail.tail))))

def WireMapStringAux(mem, key):
  match mem:
    case Map/Leaf:
      return ""
    case Map/Node:
      left = WireMapStringAux(mem.left, 2 * key) # TODO: Fix key calculation
      right = WireMapStringAux(mem.right, 2 * key + 1)
      val = mem.value
      match val:
        case Maybe/None:
          match left:
            case String/Nil:
              return right
            case String/Cons:
              match right:
                case String/Nil:
                  return String/Cons(left.head, left.tail)
                case String/Cons:
                  return String/concat(String/Cons(left.head, left.tail), 
                         String/concat(", ",
                                       String/Cons(right.head, right.tail)))
        case Maybe/Just:
          argString = String/Cons(key + 71, "")
          wire = val.val(Term/Const(key + 1))
          match left:
            case String/Nil:
              match right:
                case String/Nil:
                  return wire(argString)
                case String/Cons:
                  return wire(String/concat(argString, 
                         String/concat(", ",
                           String/Cons(right.head, right.tail))))
            case String/Cons:
              match right:
                case String/Nil:
                  return wire(String/concat(String/Cons(left.head, left.tail), 
                         String/concat(", ",
                                       argString)))
                case String/Cons:
                  return wire(String/concat(String/Cons(left.head, left.tail), 
                         String/concat(", ",
                         String/concat(argString,
                         String/concat(", ",
                                       String/Cons(right.head, right.tail))))))

def WireMapString(mem):
  return String/concat(String/Cons('{', WireMapStringAux(mem, 0)), "}")
  
# Print a map of term stacks.
def StackMapStringAux(mem, key):
  match mem:
    case Map/Leaf:
      return ""
    case Map/Node:
      left = StackMapStringAux(mem.left, 2 * key) # TODO: Fix key calculation
      right = StackMapStringAux(mem.right, 2 * key + 1)
      val = mem.value
      match val:
        case Maybe/None:
          match left:
            case String/Nil:
              return right
            case String/Cons:
              match right:
                case String/Nil:
                  return String/Cons(left.head, left.tail)
                case String/Cons:
                  return String/concat(String/Cons(left.head, left.tail), 
                         String/concat(", ",
                                       String/Cons(right.head, right.tail)))
        case Maybe/Just:
          argString = String/Cons(key + 71, String/concat(" → [", String/concat(TermArgsString(val.val), "]")))
          match left:
            case String/Nil:
              match right:
                case String/Nil:
                  return argString
                case String/Cons:
                  return String/concat(argString, 
                         String/concat(", ",
                           String/Cons(right.head, right.tail)))
            case String/Cons:
              match right:
                case String/Nil:
                  return String/concat(String/Cons(left.head, left.tail), 
                         String/concat(", ",
                                       argString))
                case String/Cons:
                  return String/concat(String/Cons(left.head, left.tail), 
                         String/concat(", ",
                         String/concat(argString,
                         String/concat(", ",
                                       String/Cons(right.head, right.tail)))))

def StackMapString(mem):
  return String/concat(String/Cons('{', StackMapStringAux(mem, 0)), "}")

# Relational Machine Calculus Programs
type RMCProg:
  # Do nothing/move on
  Skip
  # Compose a list of relations
  Comp {args}
  # Repeate relation infinitely
  Rep {~fst}
  # Chose between several relations
  Or {args}
  # Bind fresh unification variable (analagous to `fresh` in kanren)
  # fst should be lambda expression. This is HOAS (is there a way to get this to work with `fold`, etc?)
  Ex {fst}
  # Push value onto stack at address
  Push {val, addr}
  # Pop value from stack from address
  # Value must unify with what's on the stack
  Pop {val, addr}

# Render RMCProg as a string
def RMCProgString(prog):
  match prog:
    case RMCProg/Skip:
      return "*"
    case RMCProg/Comp:
      return String/concat(String/Cons('(', RMCProgArgsString(prog.args, "; ")), ")")
    case RMCProg/Rep:
      return String/Cons('*', RMCProgString(prog.fst))
    case RMCProg/Or:
      return String/concat(String/Cons('(', RMCProgArgsString(prog.args, " + ")), ")")
    case RMCProg/Ex:
      return String/concat("fresh x.", RMCProgString(prog.fst(Term/Var(`x`, `W`))))
    case RMCProg/Push:
      return String/concat("Push(", 
             String/concat(TermString(prog.val), 
             String/concat(", ", 
             String/concat(String/Cons('#', String/Cons(prog.addr + 71, String/Nil))
                          , ")"))))
    case RMCProg/Pop:
      return String/concat("Pop(", 
             String/concat(TermString(prog.val), 
             String/concat(", ", 
             String/concat(String/Cons('#', String/Cons(prog.addr + 71, String/Nil))
                          , ")"))))

def RMCProgArgsString(args, intr):
  match args:
    case List/Nil:
      return ""
    case List/Cons:
      match args.tail:
        case List/Nil:
          return RMCProgString(args.head)
        case List/Cons:
          return String/concat(RMCProgString(args.head), 
                 String/concat(intr, 
                               RMCProgArgsString(List/Cons(args.tail.head, args.tail.tail), intr)
                               ))

# Compute the inverse of a relational program.
def duel(prog):
  match prog:
    case RMCProg/Skip:
      return RMCProg/Skip
    case RMCProg/Comp:
      return RMCProg/Comp(List/map(duel, List/reverse(prog.args)))
    case RMCProg/Rep:
      return RMCProg/Rep(duel(prog.fst))
    case RMCProg/Or:
      return RMCProg/Or(List/map(duel, prog.args))
    case RMCProg/Ex:
      return RMCProg/Ex(lambda x: duel(prog.fst(x)))
    case RMCProg/Push:
      return RMCProg/Pop(prog.val, prog.addr)
    case RMCProg/Pop:
      return RMCProg/Push(prog.val, prog.addr)

# Evaluation environment, consisting of
#   a gensym for generating fresh unification variable names
#   a map from unification variable names to unscoped lambdas pointing to where those vars are referenced.
#   a map pointing to stacks of terms (The inputs/outputs of relations)
#   the current instruction
#   the stack of future instructions
type Env:
  Env {sym, wireMap, stackMap, instr, instrStack}

# Render environment into a string for debugging
def EnvString(env):
  match env:
    case Env/Env:
      return String/concat(WireMapString(env.wireMap),
             String/Cons(  '\n',
             String/concat(StackMapString(env.stackMap),
             String/Cons(  '\n',
             String/concat(RMCProgString(env.instr),
             String/Cons(  '\n',
             String/Cons(  '[',
             String/concat(RMCProgArgsString(env.instrStack, ", "),
                           "]"
             ))))))))

def EnvStackMapString(env):
  match env:
    case Env/Env:
      return StackMapString(env.wireMap)
      

def EnvWireMapString(env):
  match env:
    case Env/Env:
      return WireMapString(env.stackMap)

def EnvRMCProgString(env):
  match env:
    case Env/Env:
      return RMCProgString(env.instr)

def EnvRMCProgArgsString(env):
  match env:
    case Env/Env:
      return RMCProgArgsString(env.instrStack, ", ")

def emptyEnv(input, prog):
  return Env/Env(0, {}, input, prog, [])

# The type of the (coinductive) evluation trees.
# Represents all branching, nonbranching, and finishing cases.
type Trace:
  Success {env}
  Branch {args}

# Take a single step of the RMC.
# Takes an Env as input and returns a single Trace layer
def step(env):
  match env:
    case Env/Env:
      match env.instr:
        case RMCProg/Skip:
          match env.instrStack:
            case List/Nil:
              # Skipping when there are no remaining instructions is a Success.
              return Trace/Success(
                      Env/Env(
                        env.sym,
                        env.wireMap,
                        env.stackMap,
                        RMCProg/Skip,
                        List/Nil))
            case List/Cons:
              # Skipping when there are remaining instructions just centers the next instruction.
              return Trace/Branch([
                      Env/Env(
                        env.sym,
                        env.wireMap,
                        env.stackMap,
                        env.instrStack.head,
                        env.instrStack.tail)])
        case RMCProg/Comp:
          # Composition just pushes the rest of the relations onto the instruction stack.
          match env.instr.args:
            case List/Nil:
              return Trace/Branch([
                        Env/Env(env.sym
                               ,env.wireMap
                               ,env.stackMap
                               ,RMCProg/Skip
                               ,env.instrStack)])
            case List/Cons:
              return Trace/Branch([
                        Env/Env(env.sym
                               ,env.wireMap
                               ,env.stackMap
                               ,env.instr.args.head
                               ,List/Cons(RMCProg/Comp(env.instr.args.tail),env.instrStack))])
        case RMCProg/Rep:
          # Rep nondeterministically either does nothing or repeats its instruction.
          # TODO: Is there a better way to do this duplication?
          {stuff1, stuff2} = (env.wireMap, env.stackMap, env.instr.fst, env.instrStack)
          (wireMap1, stackMap1, instr1, instrStack1) = stuff1
          (wireMap2, stackMap2, instr2, instrStack2) = stuff2
          return Trace/Branch([
                    Env/Env(env.sym
                           ,wireMap1
                           ,stackMap1
                           ,RMCProg/Skip
                           ,instrStack1),
                    Env/Env(env.sym
                           ,wireMap2
                           ,stackMap2
                           ,RMCProg/Comp([instr2,RMCProg/Rep(instr2)])
                           ,instrStack2)
                 ])
        case RMCProg/Or:
          # Or makes a nondeterministic choice between its instructions.
          return Trace/Branch(
                    List/map(lambda x:
                      Env/Env(env.sym
                             ,env.wireMap
                             ,env.stackMap
                             ,x
                             ,env.instrStack),
                      env.instr.args))
        case RMCProg/Ex:
          # When making a fresh variable, we make its name the current gensym. We then tie
          # that symbol to all other instances via the address space.
          return Trace/Branch([
            Env/Env(env.sym + 1
                   ,Map/set_maybe(env.wireMap, env.sym, lambda $x: (lambda z: z))
                   ,env.stackMap
                   ,env.instr.fst(Term/Var(env.sym, $x))
                   ,env.instrStack)
          ])
        case RMCProg/Push:
          return Trace/Branch([
            Env/Env(env.sym
                   ,env.wireMap
                   ,Map/map_def_maybe(env.stackMap, env.instr.addr, lambda x: List/Cons(env.instr.val, x), [])
                   ,RMCProg/Skip
                   ,env.instrStack)
          ])
        case RMCProg/Pop:
          # First, check what's being popped into
          match env.instr.val:
          
          
            case Term/Var:
              # Try popping wire from adress space;
              (wire, wireMapPrime) = Map/get_drop_maybe(env.wireMap, env.instr.val.name)
              match wire:
                # If the wire doesn't exist, then substitution must have already occured.
                case Maybe/None:
                  return Trace/Branch([
                    Env/Env(env.sym
                           ,wireMapPrime
                           ,env.stackMap
                           ,RMCProg/Pop(env.instr.val.val, env.instr.addr)
                           ,env.instrStack)
                    ])
                # If the wire does exist, then it's avaliable for substitution
                case Maybe/Just:
                  # Pop term off stack
                  (poppedTerm, stackMapPrime) = Map/pop_stack_maybe(env.stackMap, env.instr.addr)
                  match poppedTerm:
                    # If there's nothing to pop, then fail.
                    case Maybe/None:
                      return Trace/Branch([])
                    case Maybe/Just:
                      match poppedTerm.val:
                        case Term/Var:
                          switch (env.instr.val.name == poppedTerm.val.name):
                            case 0:
                              return wire.val(Term/Var(poppedTerm.val.name, poppedTerm.val.val), 
                                Trace/Branch([
                                  Env/Env(env.sym
                                         ,wireMapPrime
                                         ,stackMapPrime
                                         ,RMCProg/Skip
                                         ,env.instrStack)
                                ])
                              )
                            case _:
                              # If the popped variable and the popped-to variable are the same, don't modify wire.
                              return Trace/Branch([
                                Env/Env(env.sym
                                       ,Map/set_maybe(wireMapPrime, env.instr.val.name, wire)
                                       ,stackMapPrime
                                       ,RMCProg/Skip
                                       ,env.instrStack)
                              ])
                        case Term/Const:
                          ### Working on this case
                          #return Trace/Branch([])
                          return wire.val(Term/Const(poppedTerm.val.str), 
                            Trace/Branch([
                              Env/Env(env.sym
                                     ,wireMapPrime
                                     ,stackMapPrime
                                     ,RMCProg/Skip
                                     ,env.instrStack)
                            ])
                          )
                        case Term/Fun:
                          return wire.val(Term/Fun(poppedTerm.val.str, poppedTerm.val.args), 
                            Trace/Branch([
                              Env/Env(env.sym
                                     ,wireMapPrime
                                     ,stackMapPrime
                                     ,RMCProg/Skip
                                     ,env.instrStack)
                            ])
                          )
                          
                          
            case Term/Const:
              # Pop term off stack
              (poppedTerm, stackMapPrime) = Map/pop_stack_maybe(env.stackMap, env.instr.addr)
              match poppedTerm:
                # If there's nothing to pop, then fail.
                case Maybe/None:
                  return Trace/Branch([])
                case Maybe/Just:
                  match poppedTerm.val:
                    case Term/Var:
                      # Try popping wire from adress space;
                      (wire, wireMapPrime) = Map/get_drop_maybe(env.wireMap, poppedTerm.val.name)
                      match wire:
                        # If the wire doesn't exist, then substitution must have already occured.
                        case Maybe/None:
                          return Trace/Branch([
                            Env/Env(env.sym
                                   ,wireMapPrime
                                   ,Map/map_maybe(stackMapPrime, env.instr.addr, lambda x: List/Cons(poppedTerm.val.val, x))
                                   ,RMCProg/Pop(Term/Const(env.instr.val.str), env.instr.addr)
                                   ,env.instrStack)
                            ])
                        # If the wire does exist, then it's avaliable for substitution
                        case Maybe/Just:
                          return wire.val(Term/Const(env.instr.val.str),
                              Trace/Branch([Env/Env(env.sym
                                     ,wireMapPrime
                                     ,stackMapPrime
                                     ,RMCProg/Skip
                                     ,env.instrStack)])
                              )
                    case Term/Const:
                      switch (poppedTerm.val.str == env.instr.val.str):
                        case 0:
                          return Trace/Branch([])
                        case _:
                          return Trace/Branch([
                                    Env/Env(env.sym
                                           ,env.wireMap
                                           ,stackMapPrime
                                           ,RMCProg/Skip
                                           ,env.instrStack)
                                    ])
                    case Term/Fun:
                      return Trace/Branch([])
              
              
            case Term/Fun:
              # Pop term off stack
              (poppedTerm, stackMapPrime) = Map/pop_stack_maybe(env.stackMap, env.instr.addr)
              match poppedTerm:
                # If there's nothing to pop, then fail.
                case Maybe/None:
                  return Trace/Branch([])
                case Maybe/Just:
                  match poppedTerm.val:
                    case Term/Var:
                      # Try popping wire from adress space;
                      (wire, wireMapPrime) = Map/get_drop_maybe(env.wireMap, poppedTerm.val.name)
                      match wire:
                        # If the wire doesn't exist, then substitution must have already occured.
                        case Maybe/None:
                          return Trace/Branch([
                            Env/Env(env.sym
                                   ,wireMapPrime
                                   ,Map/map_maybe(stackMapPrime, env.instr.addr, lambda x: List/Cons(poppedTerm.val.val, x))
                                   ,RMCProg/Pop(Term/Fun(env.instr.val.str, env.instr.val.args), env.instr.addr)
                                   ,env.instrStack)
                            ]) 
                        # If the wire does exist, then it's avaliable for substitution
                        case Maybe/Just:
                          return wire.val(Term/Const(env.instr.val.str),
                              Trace/Branch([Env/Env(env.sym
                                     ,wireMapPrime
                                     ,stackMapPrime
                                     ,RMCProg/Skip
                                     ,env.instrStack)
                              ]))
                    case Term/Const:
                      return Trace/Branch([])
                    case Term/Fun:
                      (len1, args1) = List/length(env.instr.val.args)
                      (len2, args2) = List/length(poppedTerm.val.args)
                      switch ((poppedTerm.val.str == env.instr.val.str) & (len1 == len2)):
                        case 0:
                          return Trace/Branch([])
                        case _:
                          # When two function symbols are to be unified, turn arguments into pop instructions and
                          # push all args of popped term onto stack.
                          # Note: Maybe this could be simplified by having pop (and push) take lists instead
                          #       of single arguments.
                          return Trace/Branch([
                                    Env/Env(env.sym
                                           ,env.wireMap
                                           ,Map/map_maybe(stackMapPrime, env.instr.addr, lambda x: List/concat(args2, x))
                                           ,RMCProg/Comp(List/map(lambda x: RMCProg/Pop(x, env.instr.addr), args1))
                                           ,env.instrStack)
                                    ])

# Takes a trace layer and returns its underlying list of environments
def unlayerTrace(tr):
  match tr:
    case Trace/Success:
      return [tr.env]
    case Trace/Branch:
      return tr.args

def dfstep(envList):
  match envList:
    case List/Nil:
      return envList
    case List/Cons:
      return List/concat(unlayerTrace(step(envList.head)), envList.tail)

def bfstep(envList):
  match envList:
    case List/Nil:
      return envList
    case List/Cons:
      return List/concat(envList.tail, unlayerTrace(step(envList.head)))

def lstep(envList):
  return List/flatten(List/map(lambda x: unlayerTrace(step(x)), envList))

def n_steps(n, envList):
  switch n:
    case 0:
      return envList
    case _:
      return n_steps(n - 1, dfstep(envList))

#### Examples and Tests ####

# Bidirectional addition example.
# Adds two numbers (stored in a1 and a2) and returns their sum (stored in a2).
# Numbers are encoded as unary terms. 2 is s(s(z)), etc.
def additionEx(a1, a2):
  return RMCProg/Comp([
      # Push "true" onto the running stack. This is the only way the program can be entered (backward: exited)
      RMCProg/Push(Term/Const(`true`), `rnin`),
      # Two options, the num in a1 is either 0 or 1 + x.
      RMCProg/Rep(RMCProg/Or([
        RMCProg/Comp([
          # If a is zero, pop it
          RMCProg/Pop(Term/Const(`z`), a1), 
          RMCProg/Pop(Term/Const(`true`), `rnin`), 
          # This is the only way for running to be set to "false"
          RMCProg/Push(Term/Const(`fals`), `rnin`)
        ]),
        RMCProg/Comp([
          # If a is 1 + x, replace it with x and add 1 + to b.
          RMCProg/Ex(lambda d: RMCProg/Comp([RMCProg/Pop(Term/Fun(`s`, [d]), a1), RMCProg/Push(d, a1)])), 
          RMCProg/Ex(lambda z2: RMCProg/Comp([RMCProg/Pop(z2, a2), RMCProg/Push(Term/Fun(`s`, [z2]), a2)]))
        ])
      ])),
      # The only way to exit the program (backward: enter) is if running is set to false.
      RMCProg/Pop(Term/Const(`fals`), `rnin`)
    ])

# Example input; a = 3 and b = 2
def exCtx():
  return Map/set_maybe(Map/set_maybe({}
           , `a`, [Term/Fun(`s`, [Term/Fun(`s`, [Term/Fun(`s`, [Term/Const(`z`)])])])] )
           , `b`, [Term/Fun(`s`, [Term/Fun(`s`, [Term/Const(`z`)])])] )

def printEnvs(envs):
  match envs:
    case List/Nil:
      return ""
    case List/Cons:
      return String/concat(EnvString(envs.head), 
             String/concat("|||",
                         printEnvs(envs.tail)
             ))

def FirstEnvString(f, envs):
  match envs:
    case List/Nil:
      return ""
    case List/Cons:
      return f(envs.head)

def main():
  wire = (lambda $x: lambda z: z, $x)
  return (wire, wire)

def main2():
  state = n_steps(8, [emptyEnv(exCtx(), additionEx(`a`, `b`))])
  match state:
    case List/Nil:
      return "Empty"
    case List/Cons:
      env = state.head
      #return EnvString(env)
      match env:
        case Env/Env:
          #return WireMapString(env.wireMap)
          #return StackMapString(env.stackMap)
          return (env.instr)
          #return RMCProgArgsString(env.instrStack, ", ")

#  return n_steps(7, [emptyEnv(exCtx(), additionEx(`a`, `b`))])

# EnvString
# EnvWireMapString
# EnvStackMapString
# EnvRMCProgString
# EnvRMCProgArgsString

#def EnvRMCProgString(env):
#  match env:
#    case Env/Env:
#      return RMCProgString(env.instr)

# return TermString(Term/Fun(`s`, [Term/Fun(`s`, [Term/Fun(`s`, [Term/Const(`z`)])])]))

#  return [emptyEnv(exCtx(), additionEx(`a`, `b`))]

#  return unlayerTrace(step(emptyEnv(exCtx(), additionEx(`a`, `b`))))














