--------------------- MODULE vchain3 -----------------------------
(****************************************************************)
(* Replicated storage with chain replication *)
(***************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS N, C, STOP, FAILNUM
ASSUME N-FAILNUM>=1 /\ STOP<5 /\ 0<=FAILNUM /\ FAILNUM<=2
Nodes == 1..N
Clients == N+1..N+C \* \* should give different ID space to Client
Procs == 1..N+C
Configurator == N+C+1

(* 
--algorithm voldchain
{
  variable FailNum=FAILNUM,
           msg=[j \in Procs |-> <<>>],
           up=[n \in Nodes |-> TRUE], \*\*Initially all nodes are up  
           db=\* \* db is single record only
              [n \in Nodes |-> [ver|->-1, val|->-1, cli|->-1]],
           chain= <<>>;

  define
  {UpNodes == {n \in Nodes : up[n]=TRUE}
   InChain(s) == s \in ChainNodes
   ChainNodes == {i : j \in chain}
   FreeUpNode == CHOOSE p \in UpNodes : InChain(p)=FALSE
\*   GetIndex(s) == \* Assumes InChain(s), returns index of s in chain
   
\*   GetNext(s) == \* Assumes InChain(s), returns successor of s in chain
   
  }


  fair process (c \in Clients)
  variable cntr=0, hver=-1;
  {
   C0: await(Len(chain)>0);
   CL: while(cntr<=STOP){

cntr:=cntr+1;
         
       }
  }

  \*fair process (n \in Nodes)
  \*{
  \*ND: while (TRUE){
    \*  either
      \*NM: {     
      
      \*n:=1;
            
        \*  } or
  \*    NDF: {  
    \*        if (FailNum>0 /\ up[self]=TRUE){ \*\* Storage node can fail 
      \*        up[self]:=FALSE; 
        \*      FailNum:=FailNum-1;}
    \*        else if (up[self]=FALSE){ \* \* Or recover
    \*          up[self]:=TRUE;
      \*        FailNum:=FailNum+1;}
      \*     }
    \*  }
  \*}

  fair process(p=Configurator)
  {
  P: while(TRUE) {
     if (Len(chain)<3) {
        chain:=Append(chain,FreeUpNode);
        if (Len(chain)>1) {
           db[chain[Len(chain)]]:=db[chain[Len(chain)-1]];
        } 
        
     }
    \* else {
           \* \* Delete down node
      \*      }
  
     
     
     
     }
  }
}
  

*)
\* BEGIN TRANSLATION
VARIABLES FailNum, msg, up, db, chain, pc

(* define statement *)
UpNodes == {n \in Nodes : up[n]=TRUE}
InChain(s) == s \in ChainNodes
ChainNodes == {i : j \in chain}
FreeUpNode == CHOOSE p \in UpNodes : InChain(p)=FALSE

VARIABLES cntr, hver

vars == << FailNum, msg, up, db, chain, pc, cntr, hver >>

ProcSet == (Clients) \cup {Configurator}

Init == (* Global variables *)
        /\ FailNum = FAILNUM
        /\ msg = [j \in Procs |-> <<>>]
        /\ up = [n \in Nodes |-> TRUE]
        /\ db = [n \in Nodes |-> [ver|->-1, val|->-1, cli|->-1]]
        /\ chain = <<>>
        (* Process c *)
        /\ cntr = [self \in Clients |-> 0]
        /\ hver = [self \in Clients |-> -1]
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "C0"
                                        [] self = Configurator -> "P"]

C0(self) == /\ pc[self] = "C0"
            /\ (Len(chain)>0)
            /\ pc' = [pc EXCEPT ![self] = "CL"]
            /\ UNCHANGED << FailNum, msg, up, db, chain, cntr, hver >>

CL(self) == /\ pc[self] = "CL"
            /\ IF cntr[self]<=STOP
                  THEN /\ cntr' = [cntr EXCEPT ![self] = cntr[self]+1]
                       /\ pc' = [pc EXCEPT ![self] = "CL"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ cntr' = cntr
            /\ UNCHANGED << FailNum, msg, up, db, chain, hver >>

c(self) == C0(self) \/ CL(self)

P == /\ pc[Configurator] = "P"
     /\ IF Len(chain)<3
           THEN /\ chain' = Append(chain,FreeUpNode)
                /\ IF Len(chain')>1
                      THEN /\ db' = [db EXCEPT ![chain'[Len(chain')]] = db[chain'[Len(chain')-1]]]
                      ELSE /\ TRUE
                           /\ db' = db
           ELSE /\ TRUE
                /\ UNCHANGED << db, chain >>
     /\ pc' = [pc EXCEPT ![Configurator] = "P"]
     /\ UNCHANGED << FailNum, msg, up, cntr, hver >>

p == P

Next == p
           \/ (\E self \in Clients: c(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Clients : WF_vars(c(self))
        /\ WF_vars(p)

\* END TRANSLATION

\* invariant for all nodes, the ver and val should match. if there is consistency however, val > ver can happen. 
\* Because the client read an old ver, and cntr is incrementing as usual and ver becomes lower than cntr=val.

Consistent == \A p \in Nodes: \A m \in db[p]: m.ver=m.val
\*\* It is possible to write alternative Consistent properties,
\*\* this one is shortcut leveraging the way the client stores items to the storage system.
======================================================================
 



