// SunSpider access-nbody.js

var PI = 3.141592653589793;
var SOLAR_MASS = 4 * PI * PI;
var DAYS_PER_YEAR = 365.24;

/*: #define tyBody
    {Dict|(and (dom v {"x","y","z","vx","vy","vz","mass"})
               (Num (sel v "x")) (Num (sel v "y"))
               (Num (sel v "z")) (Num (sel v "vx"))
               (Num (sel v "vy")) (Num (sel v "vz"))
               (Num (sel v "mass")))} */ "#define";

/*: #define ctorBody
    [;Lnew] (this:Ref(Lnew),x:Num,y:Num,z:Num,vx:Num,vy:Num,vz:Num,mass:Num)
          / (Lnew |-> _:Empty > lBodyProto)
         -> Ref(Lnew) / (Lnew |-> _:tyBody > lBodyProto) */ "#define";

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

/*: #define tyPlanet [;L] () / () -> Ref(L) / (L: tyBody > lBodyProto) */ "#define";

var Jupiter = function() /*: tyPlanet */ {
   return new /*: L */ Body(
      4.84143144246472090e+00,
      -1.16032004402742839e+00,
      -1.03622044471123109e-01,
      1.66007664274403694e-03 * DAYS_PER_YEAR,
      7.69901118419740425e-03 * DAYS_PER_YEAR,
      -6.90460016972063023e-05 * DAYS_PER_YEAR,
      9.54791938424326609e-04 * SOLAR_MASS
   );
};

function Saturn() /*: tyPlanet */ {
   return new /*: L */ Body(
      8.34336671824457987e+00,
      4.12479856412430479e+00,
      -4.03523417114321381e-01,
      -2.76742510726862411e-03 * DAYS_PER_YEAR,
      4.99852801234917238e-03 * DAYS_PER_YEAR,
      2.30417297573763929e-05 * DAYS_PER_YEAR,
      2.85885980666130812e-04 * SOLAR_MASS
   );
}

function Uranus() /*: tyPlanet */ {
   return new /*: L */ Body(
      1.28943695621391310e+01,
      -1.51111514016986312e+01,
      -2.23307578892655734e-01,
      2.96460137564761618e-03 * DAYS_PER_YEAR,
      2.37847173959480950e-03 * DAYS_PER_YEAR,
      -2.96589568540237556e-05 * DAYS_PER_YEAR,
      4.36624404335156298e-05 * SOLAR_MASS
   );
}

function Neptune() /*: tyPlanet */ {
   return new /*: L */ Body(
      1.53796971148509165e+01,
      -2.59193146099879641e+01,
      1.79258772950371181e-01,
      2.68067772490389322e-03 * DAYS_PER_YEAR,
      1.62824170038242295e-03 * DAYS_PER_YEAR,
      -9.51592254519715870e-05 * DAYS_PER_YEAR,
      5.15138902046611451e-05 * SOLAR_MASS
   );
}

function Sun() /*: tyPlanet */ {
   return new /*: L */ Body(0.0, 0.0, 0.0, 0.0, 0.0, 0.0, SOLAR_MASS);
}
