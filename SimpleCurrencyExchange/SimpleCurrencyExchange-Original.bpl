// Simple Currency Exchange Application
// It has 4 transactions 
// The save trade transaction is an SQL insert this why the assume must always execute together with the writes (i.e., CAS)

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

procedure {:atomic}{:layer 2}  saveTrade({:linear "uid"} uid:Uid,  {:linear "tid"} tid: Tid, curFr:int, curTo:int, sAmt:int, bAmt:int, rate:int, tiPl:int, oCount:int)
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
procedure{:yields}{:layer 1} {:refines "saveTrade"} SaveTrade({:linear "uid"} uid:Uid, {:linear "tid"} tid: Tid, curFr:int, curTo:int, sAmt:int, bAmt:int, rate:int, tiPl:int, oCount:int);

///////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2} viewTrade({:linear "uid"} uid:Uid, tid: Tid) returns (cpTradeContent:[int]int)
{
  assume(uid != NoUser);
  assume(tradeUser[tid] != NoUser);

  cpTradeContent := tradeContents[tid];
}
procedure {:yields}{:layer 1} {:refines "viewTrade"} ViewTrade({:linear "uid"} uid:Uid, tid: Tid) returns (cpTradeContent:[int]int);

///////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2} viewTradeUser({:linear "uid"} uid:Uid, tid: Tid) returns (cpTradeUser:Uid)
{
  assume(uid != NoUser);
  assume(tradeUser[tid] != NoUser);

  cpTradeUser := tradeUser[tid]; 
}
procedure {:yields}{:layer 1} {:refines "viewTradeUser"} ViewTradeUser({:linear "uid"} uid:Uid, tid: Tid) returns (cpTradeUser:Uid);

///////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2} getTradeTimeStamp({:linear "uid"} uid:Uid, tid: Tid) returns (timeTrade:int)
{
  assume(uid != NoUser);
  assume(tradeUser[tid] != NoUser);

  timeTrade:=tradeContents[tid][cstTiPl]; 
}
procedure {:yields}{:layer 1} {:refines "getTradeTimeStamp"} GetTradeTimeStamp({:linear "uid"} uid:Uid, tid: Tid) returns (timeTrade:int);
