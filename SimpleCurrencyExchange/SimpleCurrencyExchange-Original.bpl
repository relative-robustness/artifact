// Simple Currency Exchange Application
// A trade can be accessed by only the process that added it

type Uid;

function {:builtin "MapConst"} MapConstBool(bool) : [Uid]bool;
function {:inline} {:linear "uid"} TidCollector(x: Uid) : [Uid]bool
{
  MapConstBool(false)[x := true]
}


// shared variables
var {:layer 0,2} tradeContents: [int][int]int;
var {:layer 0,2} tradeUser: [Uid]int;

// constants 
const unique cstCurFr:int;
const unique cstCurTo  :int; 
const unique cstsAmt   :int;
const unique cstbAmt   :int;
const unique cstRate   :int;
const unique cstTiPl   :int;
const unique cstoCount :int;

const unique Owner : Uid;


procedure {:atomic}{:layer 2}  saveTrade({:linear "uid"} uid:Uid, curFr:int, curTo:int, sAmt:int, bAmt:int, rate:int, tiPl:int, oCount:int)
modifies tradeUser, tradeContents;
{  
   assume(uid != Owner);
   var tid : int;
   tid = tradeUser[uid] + 1;
   tradeUser[uid] := tid;
   
   tradeContents[tid][cstCurFr] := curFr;
   tradeContents[tid][cstCurTo] := curTo;
   tradeContents[tid][cstsAmt] := sAmt;
   tradeContents[tid][cstbAmt] := bAmt;
   tradeContents[tid][cstRate]:= rate;
   tradeContents[tid][cstTiPl] := tiPl;
   tradeContents[tid][cstoCount] := oCount;
   
}
procedure{:yields}{:layer 1} {:refines "saveTrade"} SaveTrade({:linear "uid"} uid:Uid, curFr:int, curTo:int, sAmt:int, bAmt:int, rate:int, tiPl:int, oCount:int);


procedure {:atomic}{:layer 2} viewTrade({:linear "tid"} uid:Uid, tid: int) returns (cpTradeContent:[int]int)
{
  assume(uid == Owner);
  cpTradeContent := tradeContents[tid];
}
procedure {:yields}{:layer 1} {:refines "viewTrade"} ViewTrade({:linear "tid"} uid:Uid, tid: int) returns (cpTradeContent:[int]int);


procedure {:atomic}{:layer 2} viewTradeUser({:linear "tid"} uid:Uid, tid: int) returns (cpTradeUser:Uid)
{
  assume(uid == Owner);
  cpTradeUser := tradeUser[tid]; 
}
procedure {:yields}{:layer 1} {:refines "viewTradeUser"} ViewTradeUser({:linear "tid"} uid:Uid, tid: int) returns (cpTradeUser:Uid);


procedure {:atomic}{:layer 2} getTradeTimeStamp({:linear "tid"} uid:Uid, tid: int) returns (timeTrade:int)
{
  assume(uid == Owner);
  timeTrade:=tradeContents[tid][cstTiPl]; 
}
procedure {:yields}{:layer 1} {:refines "getTradeTimeStamp"} GetTradeTimeStamp({:linear "tid"} uid:Uid, tid: int) returns (timeTrade:int);
