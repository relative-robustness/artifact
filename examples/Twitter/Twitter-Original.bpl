// Twitter Application
// It has 3 transactions: register, fellowUser, and addTweet

type Pid;
type Uid;

function {:builtin "MapConst"} MapConstBool(bool) : [Pid]bool;
function {:inline} {:linear "pid"} PidCollector(x: Pid) : [Pid]bool
{
  MapConstBool(false)[x := true]
}

function {:builtin "MapConst"} MapConstBool2(bool) : [Uid]bool;
function {:inline} {:linear "uid"} UidCollector(x: Uid) : [Uid]bool
{
  MapConstBool2(false)[x := true]
}

var {:layer 0,2} RegistredUsers: [Uid]bool;
var {:layer 0,2} UserPassword: [Uid]int;
var {:layer 0,2} UserFollow: [Uid][Uid]bool;
var {:layer 0,2} UserTweetFollowers: [Uid][Uid]int;

///////////////////////////////////////////////////////////////////////////////
/// Twitter transactions
///////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}  register(uid:Uid, p: int)
modifies RegistredUsers, UserPassword;
{  
    assume (!RegistredUsers[uid] && p != 0);
    
	RegistredUsers[uid] := true; 
    UserPassword[uid] := p;
}
procedure{:yields}{:layer 1} {:refines "register"} Register(uid:Uid, p: int);
ensures {:layer 1} ( (!old(RegistredUsers[uid]) && p != 0) ==> (RegistredUsers[uid] && UserPassword[uid] == p) );

///////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}  fellowUser({:linear "uid"} uid1:Uid, uid2:Uid)
modifies UserFollow;
{  
    assume (!UserFollow[uid1][uid2] && RegistredUsers[uid1] && RegistredUsers[uid2] && uid1 != uid2);
    
	UserFollow[uid1][uid2] := true; 
}
procedure{:yields}{:layer 1} {:refines "fellowUser"} FellowUser({:linear "uid"} uid1:Uid, uid2:Uid);
ensures {:layer 1} ( (!old(UserFollow[uid1][uid2]) && RegistredUsers[uid1] && RegistredUsers[uid2] && uid1 != uid2) ==> UserFollow[uid1][uid2] );

///////////////////////////////////////////////////////////////////////////////

procedure {:atomic}{:layer 2}  addTweet({:linear "uid"} uid:Uid, tweet: int)
modifies UserTweetFollowers;
{  
    var copyTweet1, copyTweet2 : [Uid]int;	

    assume (RegistredUsers[uid] && tweet != 0);
      
    copyTweet1 := UserTweetFollowers[uid];
	UserTweetFollowers[uid]  := copyTweet2;

    assume(forall uid0:Uid :: UserFollow[uid0][uid] ==> (UserTweetFollowers[uid][uid0] == copyTweet1[uid0]  + tweet));

    assume(forall uid0:Uid :: !UserFollow[uid0][uid] ==> (UserTweetFollowers[uid][uid0] == copyTweet1[uid0])); 
}
procedure{:yields}{:layer 1} {:refines "addTweet"} AddTweet({:linear "uid"} uid:Uid, tweet: int);
ensures {:layer 1} ( (RegistredUsers[uid] && tweet != 0) ==> 
        ( (forall uid0:Uid :: (RegistredUsers[uid0] && UserFollow[uid0][uid]) ==> (UserTweetFollowers[uid][uid0] == old(UserTweetFollowers[uid][uid0]) + tweet)) &&
          (forall uid0:Uid :: (!RegistredUsers[uid0] || !UserFollow[uid0][uid]) ==> (UserTweetFollowers[uid][uid0] == old(UserTweetFollowers[uid][uid0]))) ) );