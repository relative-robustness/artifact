// Cassandra Lock Module
// Each lock can be controlled by at most one process at a time 
// It has three transactions: tryLock, unlock, and keepAlive
// RUN: /usr/bin/time -v --format="%e" %boogie -noinfer -typeEncoding:m -tracePOs -traceTimes  -trace  -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Oid;     // process id 
type Lnm;    // lock number 

function {:builtin "MapConst"} MapConstBool(bool) : [Lnm]bool;
function {:inline} {:linear "lnm"} LnbCollector(x: Lnm) : [Lnm]bool
{
  MapConstBool(false)[x := true]
}

var  {:layer 0,2} locksStatus   : [Lnm]Oid;

const unique ONIL: Oid;

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}  tryLock(oid: Oid, {:linear "lnm"} lnm: Lnm)
modifies locksStatus;
{    	
	assume (locksStatus[lnm] == ONIL);
	locksStatus[lnm] := oid;
}
procedure {:yields}{:layer 1} {:refines "tryLock"} TryLock(oid: Oid, {:linear "lnm"} lnm: Lnm);

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}  unlock({:linear "lnm"} lnm: Lnm)
modifies locksStatus;
{    	
	assume (locksStatus[lnm] != ONIL);
	locksStatus[lnm] := ONIL;	
}
procedure {:yields}{:layer 1} {:refines "unlock"} Unlock({:linear "lnm"} lnm: Lnm);

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}  keepAlive(oid: Oid, {:linear "lnm"} lnm: Lnm)
modifies locksStatus;
{    		
	assume (locksStatus[lnm] != ONIL);
	locksStatus[lnm] := oid;	
}
procedure {:yields}{:layer 1} {:refines "keepAlive"} KeepAlive(oid: Oid, {:linear "lnm"} lnm: Lnm);

