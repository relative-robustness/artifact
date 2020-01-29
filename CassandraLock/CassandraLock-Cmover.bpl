// Cassandra Lock Module
// Each lock can be controlled by only single process


type Oid;
type Lnm;


function {:builtin "MapConst"} MapConstBool(bool) : [Lnm]bool;
function {:inline} {:linear "lnm"} nbActsCollector(x: Lnm) : [Lnm]bool
{
  MapConstBool(false)[x := true]
}


var  {:layer 0,2} locksStatus   : [Lnm]Oid;

const unique ONIL: Oid;


procedure {:right}{:layer 2}  tryLockR(oid: Oid, {:linear "lnm"} lnm: Lnm)
{    	
	assume (locksStatus[lnm] == ONIL);
}
procedure {:yields}{:layer 1} {:refines "tryLockR"} TryLockR(oid: Oid, {:linear "lnm"} lnm: Lnm);

procedure {:right}{:layer 2}  tryLockW(oid: Oid, {:linear "lnm"} lnm: Lnm)
modifies locksStatus;
{    	
	locksStatus[lnm] := oid;
}
procedure {:yields}{:layer 1} {:refines "tryLockW"} TryLockW(oid: Oid, {:linear "lnm"} lnm: Lnm);


procedure {:right}{:layer 2}  unlockR({:linear "lnm"} lnm: Lnm)
{    	
	assume (locksStatus[lnm] != ONIL);	
}
procedure {:yields}{:layer 1} {:refines "unlockR"} UnlockR({:linear "lnm"} lnm: Lnm);

procedure {:right}{:layer 2}  unlockW({:linear "lnm"} lnm: Lnm)
modifies locksStatus;
{    	
	locksStatus[lnm] := ONIL;	
}
procedure {:yields}{:layer 1} {:refines "unlockW"} UnlockW({:linear "lnm"} lnm: Lnm);


procedure {:right}{:layer 2}  keepAliveR(oid: Oid, {:linear "lnm"} lnm: Lnm)
{    		
	assume (locksStatus[lnm] != ONIL);	
}
procedure {:yields}{:layer 1} {:refines "keepAliveR"} KeepAliveR(oid: Oid, {:linear "lnm"} lnm: Lnm);


procedure {:right}{:layer 2}  keepAliveW(oid: Oid, {:linear "lnm"} lnm: Lnm)
modifies locksStatus;
{    		
	locksStatus[lnm] := oid;	
}
procedure {:yields}{:layer 1} {:refines "keepAliveW"} KeepAliveW(oid: Oid, {:linear "lnm"} lnm: Lnm);
