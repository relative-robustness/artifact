// Betting Module
// Has two transactions: settleBet and placeBet
// settleBet can only be called by one process
// RUN: /usr/bin/time -v --format="%e" %boogie -noinfer -typeEncoding:m -tracePOs -traceTimes  -trace  -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Pid;
type Bid;

function {:builtin "MapConst"} MapConstBoolPid(bool) : [Pid]bool;
function {:inline} {:linear "Pid"} PidCollector(x: Pid) : [Pid]bool
{
  MapConstBoolPid(false)[x := true]
}

function {:builtin "MapConst"} MapConstBoolBid(bool) : [Bid]bool;
function {:inline} {:linear "Bid"} BidCollector(x: Bid) : [Bid]bool
{
  MapConstBoolBid(false)[x := true]
}

var  {:layer 0,2} betsStatus   : [Bid]int;
var  {:layer 0,2} time         : int;

const unique expiryTime   : int;
const unique P0           : Pid;  // This is the only process that can call settleBet

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}  placeBet({:linear "Pid"} pid: Pid, {:linear "Bid"} bid: Bid, amount: int)
modifies betsStatus, time;
{    
    assume (pid != P0);
    assume (time < expiryTime);
	betsStatus[bid] := amount;
	time := time + 1;
}
procedure {:yields}{:layer 1} {:refines "placeBet"} PlaceBet({:linear "Pid"} pid: Pid, {:linear "Bid"} bid: Bid, amount: int);

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}  settleBet({:linear "Pid"} pid: Pid) returns (winner:int)
modifies betsStatus, time;
{    
    var bid : Bid;
    assume (pid == P0);
    assume (time >= expiryTime);
	assume (betsStatus[bid] != 0);
	winner := betsStatus[bid];
}
procedure {:yields}{:layer 1} {:refines "settleBet"} SettleBet({:linear "Pid"} pid: Pid) returns (winner:int);