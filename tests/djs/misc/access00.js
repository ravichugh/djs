// SunSpider access-nbody.js

var PI = 3.141592653589793;
var SOLAR_MASS = 4 * PI * PI;
var DAYS_PER_YEAR = 365.24;

/*: #define tyBody
    {Dict|(and (dom v {"x","y","z","vx","vy","vz","mass"})
               (Num (sel v "x"))
               (Num (sel v "y"))
               (Num (sel v "z"))
               (Num (sel v "vx"))
               (Num (sel v "vy"))
               (Num (sel v "vz"))
               (Num (sel v "mass")))} */ "#define";

/*: #define ctorBody
    [;Lnew] (this:Ref(Lnew),x:Num,y:Num,z:Num,vx:Num,vy:Num,vz:Num,mass:Num)
          / (Lnew |-> Empty > lBodyProto)
         -> Ref(Lnew) / (Lnew |-> tyBody > lBodyProto) */ "#define";

function Body(x,y,z,vx,vy,vz,mass) /*: new ctorBody */ {
   this.x = x;
   this.y = y;
   this.z = z;
   this.vx = vx;
   this.vy = vy;
   this.vz = vz;
   this.mass = mass;
   return this;
}

////////////////////////////////////////////////////////////////////////////////

/*: #define tyOffsetMomentum
    [;L] (this:Ref(L), px:Num, py:Num, pz:Num)
       / (L |-> _:tyBody > lBodyProto, &SOLAR_MASS |-> _:Num)
      -> Ref(L) / sameType */ "#define";

Body.prototype.offsetMomentum = function(px,py,pz) /*: tyOffsetMomentum */ {
   this.vx = -px / SOLAR_MASS;
   this.vy = -py / SOLAR_MASS;
   this.vz = -pz / SOLAR_MASS;
   return this;
};
