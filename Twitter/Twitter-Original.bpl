// Twitter Application

type Pid;
type Uid;

function {:builtin "MapConst"} MapConstBool(bool) : [Pid]bool;
function {:inline} {:linear "pid"} TidCollector(x: Pid) : [Pid]bool
{
  MapConstBool(false)[x := true]
}

function {:builtin "MapConst"} MapConstBool2(bool) : [Uid]bool;
function {:inline} {:linear "uid"} TidCollector2(x: Uid) : [Uid]bool
{
  MapConstBool2(false)[x := true]
}

var {:layer 0,2} ActiveUser: [Uid]bool;
var {:layer 0,2} UserPassword: [Uid]int;
var {:layer 0,2} UserFollow: [Uid][Uid]bool;
var {:layer 0,2} UserTweetFollowers: [Uid][Uid]int;



procedure {:atomic}{:layer 2}  addUser(uid:Uid, p: int)
modifies ActiveUser, UserPassword;
{  
    assume (!ActiveUser[uid] && p != 0);
    
	ActiveUser[uid] := true; 
    UserPassword[uid] := p;
}
procedure{:yields}{:layer 1} {:refines "addUser"} AddUser(uid:Uid, p: int);
ensures {:layer 1} ( (!old(ActiveUser[uid]) && p != 0) ==> (ActiveUser[uid] && UserPassword[uid] == p) );


procedure {:atomic}{:layer 2}  fellowUser({:linear "uid"} uid1:Uid, uid2:Uid)
modifies UserFollow;
{  
    assume (!UserFollow[uid1][uid2] && ActiveUser[uid1] && ActiveUser[uid2] && uid1 != uid2);
    
	UserFollow[uid1][uid2] := true; 
}
procedure{:yields}{:layer 1} {:refines "fellowUser"} FellowUser({:linear "uid"} uid1:Uid, uid2:Uid);
ensures {:layer 1} ( (!old(UserFollow[uid1][uid2]) && ActiveUser[uid1] && ActiveUser[uid2] && uid1 != uid2) ==> UserFollow[uid1][uid2] );


procedure {:atomic}{:layer 2}  addTweet({:linear "uid"} uid:Uid, tweet: int)
modifies UserTweetFollowers;
{  
    var copyTweet1, copyTweet2 : [Uid]int;	

    assume (ActiveUser[uid] && tweet != 0);
      
    copyTweet1 := UserTweetFollowers[uid];
	UserTweetFollowers[uid]  := copyTweet2;

    assume(forall uid0:Uid :: UserFollow[uid0][uid] ==> (UserTweetFollowers[uid][uid0] == copyTweet1[uid0]  + tweet));

    assume(forall uid0:Uid :: !UserFollow[uid0][uid] ==> (UserTweetFollowers[uid][uid0] == copyTweet1[uid0])); 
}
procedure{:yields}{:layer 1} {:refines "addTweet"} AddTweet({:linear "uid"} uid:Uid, tweet: int);
ensures {:layer 1} ( (ActiveUser[uid] && tweet != 0) ==> 
        ( (forall uid0:Uid :: (ActiveUser[uid0] && UserFollow[uid0][uid]) ==> (UserTweetFollowers[uid][uid0] == old(UserTweetFollowers[uid][uid0]) + tweet)) &&
          (forall uid0:Uid :: (!ActiveUser[uid0] || !UserFollow[uid0][uid]) ==> (UserTweetFollowers[uid][uid0] == old(UserTweetFollowers[uid][uid0]))) ) );