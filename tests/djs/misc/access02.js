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

////////////////////////////////////////////////////////////////////////////////

/*: (~lBody |-> tyBody > lBodyProto) */ "#weak";

////////////////////////////////////////////////////////////////////////////////

// TODO HEREHEREHERE

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
   /*: [&i |-> _:{Int|(>= v 0)}, &px |-> _:Num, &py |-> _:Num, &pz |-> _:Num,
        &size |-> _:{Int|(= v (len aBodies))},
        Lnew |-> (_:tyNBodySystem, lNBodySystemProto),
        Lbodies |-> (_:{(= v aBodies)}, lArrayProto),
        ~lBody |-> frzn
       ] -> [&i |-> sameType, &px |-> sameType, &py |-> sameType, &pz |-> sameType,
             &size |-> sameExact,
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

////////////////////////////////////////////////////////////////////////////////

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

   /*: [&i |-> _:{Int|(>= v 0)},
        L |-> (_:{(= v thisD)}, lNBodySystemProto),
        Lbodies |-> (_:{(= v aBodies)}, lArrayProto),
        &size |-> _:{Int|(= v (len aBodies))},
        ~lBody |-> frzn,
        &dx |-> _:Num
       ]
    -> [&i |-> sameType,
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
      /*: [&j |-> _:{Int|(>= v 0)},
           &size |-> _:{Int|(= v (len aBodies))},
           L |-> (_:{(= v thisD)}, lNBodySystemProto),
           Lbodies |-> (_:{(= v aBodies)}, lArrayProto),
           &bodyi |-> _:Ref(~lBody),
           ~lBody |-> frzn,
           &dx |-> _:Num
          ]
       -> [&j |-> sameType,
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


