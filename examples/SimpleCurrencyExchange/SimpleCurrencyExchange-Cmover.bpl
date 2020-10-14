// Simple Currency Exchange Application
// It has 4 transactions 
// The save trade transaction is an SQL insert this why the assume must always execute together with the writes (i.e., CAS)
// Movers check
// RUN: /usr/bin/time -v --format="%e" %boogie -noinfer -typeEncoding:m -tracePOs -traceTimes  -trace  -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Uid;
type Tid;

function {:builtin "MapConst"} MapConstBool(bool) : [Uid]bool;
function {:inline} {:linear "uid"} UidCollector(x: Uid) : [Uid]bool
{
  MapConstBool(false)[x := true]
}

function {:builtin "MapConst"} MapConstBool2(bool) : [Tid]bool;
function {:inline} {:linear "tid"} TidCollector(x: Tid) : [Tid]bool
{
  MapConstBool2(false)[x := true]
}

// shared variables
var {:layer 0,2} tradeContents: [Tid][int]int;
var {:layer 0,2} tradeUser: [Tid]Uid;

// constants 
const unique cstCurFr  :int;   // currency from
const unique cstCurTo  :int;   // currency to
const unique cstsAmt   :int;   // 
const unique cstbAmt   :int;   // 
const unique cstRate   :int;
const unique cstTiPl   :int;
const unique cstoCount :int;

const unique NoUser : Uid;

///////////////////////////////////////////////////////////////////////////////
/// SimpleCurrencyExchange transactions
///////////////////////////////////////////////////////////////////////////////

procedure {:right}{:layer 2}  saveTradeR({:linear "uid"} uid:Uid,  {:linear "tid"} tid: Tid)
modifies tradeUser, tradeContents;
{     
  assume(uid != NoUser);
  assume(tradeUser[tid] == NoUser);
}
procedure{:yields}{:layer 1} {:refines "saveTradeR"} SaveTradeR({:linear "uid"} uid:Uid, {:linear "tid"} tid: Tid);

///////////////////////////////////////////////////////////////////////////////

procedure {:right}{:layer 2}  saveTradeW({:linear "uid"} uid:Uid,  {:linear "tid"} tid: Tid, curFr:int, curTo:int, sAmt:int, bAmt:int, rate:int, tiPl:int, oCount:int)
modifies tradeUser, tradeContents;
{     
   assume(uid != NoUser);
   assume(tradeUser[tid] == NoUser);

   tradeUser[tid] := uid;
   
   tradeContents[tid][cstCurFr] := curFr;
   tradeContents[tid][cstCurTo] := curTo;
   tradeContents[tid][cstsAmt] := sAmt;
   tradeContents[tid][cstbAmt] := bAmt;
   tradeContents[tid][cstRate]:= rate;
   tradeContents[tid][cstTiPl] := tiPl;
   tradeContents[tid][cstoCount] := oCount;
   
}
procedure{:yields}{:layer 1} {:refines "saveTradeW"} SaveTradeW({:linear "uid"} uid:Uid, {:linear "tid"} tid: Tid, curFr:int, curTo:int, sAmt:int, bAmt:int, rate:int, tiPl:int, oCount:int);

///////////////////////////////////////////////////////////////////////////////

procedure {:right}{:layer 2} viewTrade({:linear "uid"} uid:Uid, tid: Tid) returns (cpTradeContent:[int]int)
{
  assume(uid != NoUser);
  assume(tradeUser[tid] != NoUser);

  cpTradeContent := tradeContents[tid];
}
procedure {:yields}{:layer 1} {:refines "viewTrade"} ViewTrade({:linear "uid"} uid:Uid, tid: Tid) returns (cpTradeContent:[int]int);

///////////////////////////////////////////////////////////////////////////////

procedure {:right}{:layer 2} viewTradeUser({:linear "uid"} uid:Uid, tid: Tid) returns (cpTradeUser:Uid)
{
  assume(uid != NoUser);
  assume(tradeUser[tid] != NoUser);

  cpTradeUser := tradeUser[tid]; 
}
procedure {:yields}{:layer 1} {:refines "viewTradeUser"} ViewTradeUser({:linear "uid"} uid:Uid, tid: Tid) returns (cpTradeUser:Uid);

///////////////////////////////////////////////////////////////////////////////

procedure {:right}{:layer 2} getTradeTimeStamp({:linear "uid"} uid:Uid, tid: Tid) returns (timeTrade:int)
{
  assume(uid != NoUser);
  assume(tradeUser[tid] != NoUser);

  timeTrade:=tradeContents[tid][cstTiPl]; 
}
procedure {:yields}{:layer 1} {:refines "getTradeTimeStamp"} GetTradeTimeStamp({:linear "uid"} uid:Uid, tid: Tid) returns (timeTrade:int);
