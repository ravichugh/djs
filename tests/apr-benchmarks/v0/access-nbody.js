// SunSpider access-nbody.js

var PI = 3.141592653589793;
var SOLAR_MASS = 4 * PI * PI;
var DAYS_PER_YEAR = 365.24;

/*: #define tyBody
    {Dict|(and (dom v {"x","y","z","vx","vy","vz","mass"})
               ((sel v "x") : Num)
               ((sel v "y") : Num)
               ((sel v "z") : Num)
               ((sel v "vx") : Num)
               ((sel v "vy") : Num)
               ((sel v "vz") : Num)
               ((sel v "mass") : Num))} */ "#define";

/*: #define ctorBody
    [;Lnew] [[this:Ref(Lnew),x:Num,y:Num,z:Num,vx:Num,vy:Num,vz:Num,mass:Num]]
          / [Lnew |-> (_:Empty, lBodyProto)]
         -> Ref(Lnew) / [Lnew |-> (_:tyBody, lBodyProto)] */ "#define";

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


/*: #define tyOffsetMomentum
    [;L] [[this:Ref(L), px:Num, py:Num, pz:Num]]
       / [L |-> (_:tyBody, lBodyProto), &SOLAR_MASS |-> _:Num]
      -> Ref(L) / sameType */ "#define";

Body.prototype.offsetMomentum = function(px,py,pz) /*: tyOffsetMomentum */ {
   this.vx = -px / SOLAR_MASS;
   this.vy = -py / SOLAR_MASS;
   this.vz = -pz / SOLAR_MASS;
   return this;
};


/*: #define objBodyIn
      &Body |-> _:Ref(lBodyObj)
    , lBodyObj |-> (_:{Dict|
         (and ((sel v "code") : ctorBody)
              ((sel v "prototype") : Ref(lBodyProto)))}, lFunctionProto)
    , lBodyProto |-> (_:Dict, lObjectProto)
    , &DAYS_PER_YEAR |-> _:Num
    , &SOLAR_MASS |-> _:Num
*/ "#define";

/*: #define objBodyOut
      &Body |-> same
    , lBodyObj |-> same
    , lBodyProto |-> same
    , &DAYS_PER_YEAR |-> same
    , &SOLAR_MASS |-> same
*/ "#define";

var Jupiter = function()
/*: [;L] [[]]   / [objBodyIn]
      -> Ref(L) / [L |-> (_:tyBody, lBodyProto), objBodyOut] */
{
   return new /*: [;L] lBodyProto */ Body(
      4.84143144246472090e+00,
      -1.16032004402742839e+00,
      -1.03622044471123109e-01,
      1.66007664274403694e-03 * DAYS_PER_YEAR,
      7.69901118419740425e-03 * DAYS_PER_YEAR,
      -6.90460016972063023e-05 * DAYS_PER_YEAR,
      9.54791938424326609e-04 * SOLAR_MASS
   );
};

// var Saturn = function()
// /*: [;L] [[]]   / [objBodyIn]
//       -> Ref(L) / [L |-> (_:tyBody, lBodyProto), objBodyOut] */
// {
//    return new /*: [;L] lBodyProto */ Body(
//       8.34336671824457987e+00,
//       4.12479856412430479e+00,
//       -4.03523417114321381e-01,
//       -2.76742510726862411e-03 * DAYS_PER_YEAR,
//       4.99852801234917238e-03 * DAYS_PER_YEAR,
//       2.30417297573763929e-05 * DAYS_PER_YEAR,
//       2.85885980666130812e-04 * SOLAR_MASS
//    );
// };
// 
// var Uranus = function()
// /*: [;L] [[]]   / [objBodyIn]
//       -> Ref(L) / [L |-> (_:tyBody, lBodyProto), objBodyOut] */
// {
//    return new /*: [;L] lBodyProto */ Body(
//       1.28943695621391310e+01,
//       -1.51111514016986312e+01,
//       -2.23307578892655734e-01,
//       2.96460137564761618e-03 * DAYS_PER_YEAR,
//       2.37847173959480950e-03 * DAYS_PER_YEAR,
//       -2.96589568540237556e-05 * DAYS_PER_YEAR,
//       4.36624404335156298e-05 * SOLAR_MASS
//    );
// };
// 
// var Neptune = function()
// /*: [;L] [[]]   / [objBodyIn]
//       -> Ref(L) / [L |-> (_:tyBody, lBodyProto), objBodyOut] */
// {
//    return new /*: [;L] lBodyProto */ Body(
//       1.53796971148509165e+01,
//       -2.59193146099879641e+01,
//       1.79258772950371181e-01,
//       2.68067772490389322e-03 * DAYS_PER_YEAR,
//       1.62824170038242295e-03 * DAYS_PER_YEAR,
//       -9.51592254519715870e-05 * DAYS_PER_YEAR,
//       5.15138902046611451e-05 * SOLAR_MASS
//    );
// };

var Sun = function()
/*: [;L] [[]]   / [objBodyIn]
      -> Ref(L) / [L |-> (_:tyBody, lBodyProto), objBodyOut] */
{
   return new /*: [;L] lBodyProto */ Body(0.0, 0.0, 0.0, 0.0, 0.0, 0.0, SOLAR_MASS);
};


/*: [~lBody |-> (tyBody, lBodyProto)] */ "#weak";


/*: #define tyNBodySystem
    {Dict|(and (dom v {"bodies"})
               ((sel v "bodies") : Ref(Lbodies)))} */ "#define";

/*: #define ctorNBodySystem
    [;Lnew,Lbodies]
            [[this:Ref(Lnew),bodies:Ref(Lbodies)]]
          / [Lnew |-> (_:Empty, lNBodySystemProto),
             Lbodies |-> (aBodies:{(and (v::Arr(Ref(~lBody))) (packed v) (> (len v) 0))}, lArrayProto),
             ~lBody |-> frzn,
             lBodyProto |-> (_:{Dict|((sel v "offsetMomentum") : tyOffsetMomentum)}, lObjectProto),
             &SOLAR_MASS |-> _:Num]
         -> Ref(Lnew)
          / [Lnew |-> (_:tyNBodySystem, lNBodySystemProto),
             Lbodies |-> same,
             ~lBody |-> frzn,
             lBodyProto |-> sameExact,
             &SOLAR_MASS |-> sameType] */ "#define";


function NBodySystem(bodies) /*: new ctorNBodySystem */ {
   this.bodies = bodies;
   var px = 0.0;
   var py = 0.0;
   var pz = 0.0;
   var size = this.bodies.length;
   var i = 0;
   /*: [&this |-> _:Ref(Lnew),
        &i |-> _:{Int|(>= v 0)}, &px |-> _:Num, &py |-> _:Num, &pz |-> _:Num,
        &size |-> _:{Int|(= v (len aBodies))},
        Lnew |-> (_:tyNBodySystem, lNBodySystemProto),
        Lbodies |-> (_:{(= v aBodies)}, lArrayProto),
        ~lBody |-> frzn
       ] -> [&i |-> sameType, &px |-> sameType, &py |-> sameType, &pz |-> sameType,
             &size |-> sameExact, &this |-> sameType,
             Lnew |-> sameExact,
             Lbodies |-> sameExact,
             ~lBody |-> frzn] */
   for (; i<size; i++){
      var b = this.bodies[i];
      /*: b lThaw1 */ "#thaw";
      var m = b.mass;
      px += b.vx * m;
      py += b.vy * m;
      pz += b.vz * m;
      /*: b (~lBody, thwd lThaw1) */ "#freeze";
   }
   var b0 = this.bodies[0];
   /*: b0 lThaw2 */ "#thaw";
   b0.offsetMomentum(px,py,pz);
   /*: b0 (~lBody, thwd lThaw2) */ "#freeze";
   return this;
}

// TODO advance. more of this.

var Math = {};
Math.sqrt = function(n) /*: [[n:Num]] -> Num */ { return n; };

/*: #define tyAdvance
    [;L,Lbodies]
         [[this:Ref(L), dt:Num]]
       / [L |-> (thisD:tyNBodySystem, lNBodySystemProto),
          Lbodies |-> (aBodies:{(and (v::Arr(Ref(~lBody)))
                                     (packed v)
                                     (> (len v) 0))}, lArrayProto),
          ~lBody |-> frzn]
      -> Top / same
*/ "#define";

NBodySystem.prototype.advance = function(dt) /*: tyAdvance */ {
   // originals didn't initialize
   var dx = 0, dy, dz, distance, mag;
   var size = this.bodies.length;

   var i = 0;

   /*: [&this |-> _:Ref(L),
        &i |-> _:{Int|(>= v 0)},
        L |-> (_:{(= v thisD)}, lNBodySystemProto),
        Lbodies |-> (_:{(= v aBodies)}, lArrayProto),
        &size |-> _:{Int|(= v (len aBodies))},
        ~lBody |-> frzn,
        &dx |-> _:Num
       ]
    -> [&this |-> sameType,
        &i |-> sameType,
        L |-> sameType,
        Lbodies |-> sameType,
        &size |-> sameType,
        ~lBody |-> frzn,
        &dx |-> sameType
       ] */
   for (; i<size; i++) {
      var bodyi = this.bodies[i];
      assert (/*: Ref(~lBody) */ bodyi);
      var j = i+1;
      /*: [&this |-> _:Ref(L),
           &j |-> _:{Int|(>= v 0)},
           &size |-> _:{Int|(= v (len aBodies))},
           L |-> (_:{(= v thisD)}, lNBodySystemProto),
           Lbodies |-> (_:{(= v aBodies)}, lArrayProto),
           &bodyi |-> _:Ref(~lBody),
           ~lBody |-> frzn,
           &dx |-> _:Num
          ]
       -> [&this |-> sameType,
           &j |-> sameType,
           &size |-> sameType,
           L |-> sameType,
           Lbodies |-> sameType,
           ~lBody |-> frzn,
           &dx |-> sameType
          ] */
      for (; j<size; j++) {
         var bodyj = this.bodies[j];
         assert (/*: Ref(~lBody) */ bodyj);

         //// original:
         ////   dx = bodyi.x - bodyj.x;
         ////   dy = bodyi.y - bodyj.y;
         ////   dz = bodyi.z - bodyj.z;

         var tmpi, tmpj;
         /*: bodyi lBodyi1 */ "#thaw";
         tmpi = bodyi.x;
         /*: bodyi (~lBody, thwd lBodyi1) */ "#freeze";
         /*: bodyj lBodyj1 */ "#thaw";
         tmpj = bodyj.x;
         /*: bodyj (~lBody, thwd lBodyj1) */ "#freeze";
         dx = tmpi - tmpj;

         //// not doing the rest manually like this ...
         
         // distance = Math.sqrt(dx*dx + dy*dy + dz*dz);
         // mag = dt / (distance * distance * distance);

         // bodyi.vx -= dx * bodyj.mass * mag;
         // bodyi.vy -= dy * bodyj.mass * mag;
         // bodyi.vz -= dz * bodyj.mass * mag;

         // bodyj.vx += dx * bodyi.mass * mag;
         // bodyj.vy += dy * bodyi.mass * mag;
         // bodyj.vz += dz * bodyi.mass * mag;
      }
   }

   // i=0;
   // /*: [] -> [] */
   // for (; i<size; i++) {
   //    var body = this.bodies[i];
   //    body.x += dt * body.vx;
   //    body.y += dt * body.vy;
   //    body.z += dt * body.vz;
   // }
};

// TODO energy
