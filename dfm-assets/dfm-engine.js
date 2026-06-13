/* DfM Casting analysis engine — aluminum, NADCA 2015.
   Pure JS. Consumes an occt-import-js mesh + raw STEP text.
   Produces per-face geometry and concern items mapped to face indices.
   Also runnable in node (module.exports) for testing. */
(function(root){
"use strict";

// ---------- small vector helpers ----------
function sub(a,b){return [a[0]-b[0],a[1]-b[1],a[2]-b[2]];}
function cross(a,b){return [a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]];}
function dot(a,b){return a[0]*b[0]+a[1]*b[1]+a[2]*b[2];}
function len(a){return Math.hypot(a[0],a[1],a[2]);}
function norm(a){var l=len(a)||1;return [a[0]/l,a[1]/l,a[2]/l];}

// ---------- Jacobi eigen-decomposition for symmetric 3x3 ----------
function eig3(A){
  var a=[[A[0],A[1],A[2]],[A[1],A[3],A[4]],[A[2],A[4],A[5]]];
  var v=[[1,0,0],[0,1,0],[0,0,1]];
  for(var iter=0;iter<50;iter++){
    // largest off-diagonal
    var p=0,q=1,max=Math.abs(a[0][1]);
    if(Math.abs(a[0][2])>max){max=Math.abs(a[0][2]);p=0;q=2;}
    if(Math.abs(a[1][2])>max){max=Math.abs(a[1][2]);p=1;q=2;}
    if(max<1e-12) break;
    var app=a[p][p],aqq=a[q][q],apq=a[p][q];
    var phi=0.5*Math.atan2(2*apq,aqq-app);
    var c=Math.cos(phi),s=Math.sin(phi);
    for(var k=0;k<3;k++){
      var akp=a[k][p],akq=a[k][q];
      a[k][p]=c*akp-s*akq; a[k][q]=s*akp+c*akq;
    }
    for(k=0;k<3;k++){
      var apk=a[p][k],aqk=a[q][k];
      a[p][k]=c*apk-s*aqk; a[q][k]=s*apk+c*aqk;
    }
    for(k=0;k<3;k++){
      var vkp=v[k][p],vkq=v[k][q];
      v[k][p]=c*vkp-s*vkq; v[k][q]=s*vkp+c*vkq;
    }
  }
  var vals=[a[0][0],a[1][1],a[2][2]];
  var vecs=[[v[0][0],v[1][0],v[2][0]],[v[0][1],v[1][1],v[2][1]],[v[0][2],v[1][2],v[2][2]]];
  return {vals:vals,vecs:vecs};
}

// ---------- unit detection from raw STEP text ----------
function detectUnit(text){
  if(/CONVERSION_BASED_UNIT[^;]*'INCH'/i.test(text)) return {name:'inch', toMM:25.4};
  if(/CONVERSION_BASED_UNIT[^;]*'FOOT'/i.test(text)) return {name:'foot', toMM:304.8};
  if(/\.MILLI\.\s*\)\s*LENGTH_UNIT/i.test(text) || /LENGTH_UNIT[^;]*\.MILLI\.\s*\.METRE\./i.test(text))
    return {name:'mm', toMM:1};
  if(/\.METRE\./i.test(text) && !/\.MILLI\./i.test(text)) return {name:'mm', toMM:1}; // SW default model mm
  return {name:'mm', toMM:1};
}

// ---------- per-face analysis ----------
// mesh: {position:Float32Array/Array, index:Array, faces:[{first,last}]}  (triangle ranges)
function analyzeFaces(mesh, scale){
  var P=mesh.position, I=mesh.index, FR=mesh.faces, faces=[];
  for(var fi=0; fi<FR.length; fi++){
    var first=FR[fi].first, last=FR[fi].last;
    var navg=[0,0,0], cen=[0,0,0], areaSum=0, tris=[];
    for(var t=first; t<=last; t++){
      var i0=I[3*t]*3, i1=I[3*t+1]*3, i2=I[3*t+2]*3;
      var v0=[P[i0],P[i0+1],P[i0+2]], v1=[P[i1],P[i1+1],P[i1+2]], v2=[P[i2],P[i2+1],P[i2+2]];
      var n=cross(sub(v1,v0),sub(v2,v0));
      var a=len(n)/2; if(a<1e-12) continue;
      var un=norm(n);
      tris.push({un:un, c:[(v0[0]+v1[0]+v2[0])/3,(v0[1]+v1[1]+v2[1])/3,(v0[2]+v1[2]+v2[2])/3],
                 a:a, v:[v0,v1,v2]});
      navg[0]+=un[0]*a; navg[1]+=un[1]*a; navg[2]+=un[2]*a;
      cen[0]+=((v0[0]+v1[0]+v2[0])/3)*a; cen[1]+=((v0[1]+v1[1]+v2[1])/3)*a; cen[2]+=((v0[2]+v1[2]+v2[2])/3)*a;
      areaSum+=a;
    }
    if(!tris.length){ faces.push({index:fi,empty:true}); continue; }
    var navgN=norm(navg);
    cen=[cen[0]/areaSum,cen[1]/areaSum,cen[2]/areaSum];
    // normal spread
    var spread=0;
    tris.forEach(function(tr){var d=Math.min(1,Math.max(-1,dot(tr.un,navgN)));var ang=Math.acos(d)*180/Math.PI; if(ang>spread)spread=ang;});

    var face={index:fi, areaMM2:areaSum*scale*scale, centroidMM:[cen[0]*scale,cen[1]*scale,cen[2]*scale],
              normal:navgN, spreadDeg:spread, kind:null, radiusMM:null, axis:null,
              radiusMinMM:null, radiusMaxMM:null};

    if(spread < 8){
      face.kind='planar';
    } else {
      // fit axis = eigenvector of normals' covariance with smallest eigenvalue
      var M=[0,0,0,0,0,0]; // xx xy xz yy yz zz
      tris.forEach(function(tr){var n=tr.un,w=tr.a;
        M[0]+=w*n[0]*n[0];M[1]+=w*n[0]*n[1];M[2]+=w*n[0]*n[2];
        M[3]+=w*n[1]*n[1];M[4]+=w*n[1]*n[2];M[5]+=w*n[2]*n[2];});
      var e=eig3(M);
      var mi=0; if(e.vals[1]<e.vals[mi])mi=1; if(e.vals[2]<e.vals[mi])mi=2;
      var axis=norm(e.vecs[mi]);
      face.axis=axis;
      // radius = distance from vertices to axis line through centroid
      var rmin=Infinity,rmax=0,rsum=0,nv=0;
      tris.forEach(function(tr){tr.v.forEach(function(p){
        var d=sub(p,cen); var proj=dot(d,axis);
        var perp=[d[0]-proj*axis[0],d[1]-proj*axis[1],d[2]-proj*axis[2]];
        var r=len(perp)*scale;
        if(r<rmin)rmin=r; if(r>rmax)rmax=r; rsum+=r; nv++;
      });});
      face.radiusMinMM=rmin; face.radiusMaxMM=rmax; face.radiusMM=rsum/nv;
      // cone if radius varies notably along the face, else cylinder
      face.kind = (rmax-rmin) > 0.15*Math.max(rmax,1e-6) ? 'conical' : 'cylindrical';
    }
    faces.push(face);
  }
  return faces;
}

// ---------- NADCA aluminum rules ----------
var PDF='NADCA-Product-Standards-for-Die-Casting.pdf';
var RULES={
  draftInsideDeg:1.9, draftOutsideDeg:0.95, draftHoleDeg:2.86,
  filletSharpMM:0.5, minWallMM:1.0,
  refDraft:   {clause:'NADCA S-4A-7-15 — Draft Requirements',            page:105},
  refFillet:  {clause:'NADCA Sec. 6, p.6-4 — Fillets',                  page:178},
  refHole:    {clause:'NADCA P-4A-9 / p.4A-31 — Cored Holes',           page:115},
  refWall:    {clause:'NADCA p.4A-31/32 — Wall Thickness',               page:115},
  refUndercut:{clause:'NADCA Sec. 3 — Parting Line, Draft & Undercuts',  page: 84}
};

// build concern items. Each item references one or more face indices (faces[]).
function buildItems(faces, pull, pullName){
  var items=[], coneFaces=[];
  faces.forEach(function(f){
    if(f.empty) return;
    if(f.kind==='planar'){
      var d=Math.min(1,Math.abs(dot(f.normal,pull)));
      var angNP=Math.acos(d)*180/Math.PI;       // 0 = face faces along pull (top), 90 = wall
      if(angNP>=55){                              // it's a side wall -> needs draft
        var draft=Math.abs(angNP-90);
        if(draft < RULES.draftInsideDeg-1e-6){
          var sev = draft < RULES.draftOutsideDeg ? 'crit':'warn';
          items.push({
            faces:[f.index], sev:sev, type:'Insufficient draft',
            current:'Measured draft ≈ '+draft.toFixed(2)+'° on this wall (relative to the '+pullName+' pull direction). '+
                    'Face area ≈ '+f.areaMM2.toFixed(1)+' mm².',
            recommended:'Aluminum minimum draft: '+RULES.draftInsideDeg.toFixed(1)+'° on inside walls (C=30), '+
                    RULES.draftOutsideDeg.toFixed(1)+'° on outside walls (C=60). Draft distance D = L/C.',
            ref:RULES.refDraft, metric:draft
          });
        }
      }
    } else if(f.kind==='cylindrical'){
      var dia=(f.radiusMM*2);
      if(f.radiusMM <= RULES.filletSharpMM){
        items.push({
          faces:[f.index], sev:'warn', type:'Near-sharp internal radius',
          current:'Cylindrical blend radius ≈ '+f.radiusMM.toFixed(2)+' mm — close to a sharp corner.',
          recommended:'Internal junctions should carry a fillet R = T to 1.25·T (T = local wall thickness). '+
                  'Sharp corners concentrate stress and crack the die.',
          ref:RULES.refFillet, metric:f.radiusMM
        });
      } else {
        items.push({
          faces:[f.index], sev:'info', type:'Cored hole / boss — verify',
          current:'Cylindrical face Ø ≈ '+dia.toFixed(2)+' mm (radius '+f.radiusMM.toFixed(2)+' mm, approx).',
          recommended:'Cored holes need their own draft (C=20 → ≈2.9° total) and adequate wall stock around the bore. '+
                  'Confirm depth-to-diameter ratio and trim allowance.',
          ref:RULES.refHole, metric:dia
        });
      }
    } else if(f.kind==='conical'){
      coneFaces.push(f.index);
    }
  });
  // group all conical faces into a single item (avoids thread spam)
  if(coneFaces.length){
    items.push({
      faces:coneFaces, sev:'info', type:'Tapered / conical faces ('+coneFaces.length+')',
      current:coneFaces.length+' conical face(s) detected and highlighted together.',
      recommended:'If these are walls, their taper acts as draft — confirm ≥ '+RULES.draftInsideDeg.toFixed(1)+
              '° (aluminum inside). If they form a thread, threads are not castable as-is and must be machined or cored.',
      ref:RULES.refDraft, metric:0
    });
  }

  // ---------- Undercut detection ----------
  // Four complementary strategies, each catching what the others miss.
  //
  // A  Backward planar:    dot(N, pull) < –0.087  → direct undercut, blocks straight pull.
  // B  Perpendicular bore: |dot(axis, pull)| < 0.5 → bore axis ⊥ pull, needs side core.
  // C  Lateral pocket wall: lateral face (|dot(N,pull)| < 0.5) that is recessed BEHIND outer
  //    geometry in its own outward-normal direction.  Even with adequate draft, the pocket it
  //    walls off cannot be released in a straight pull → side core required.
  // D  Enclosed ceiling:   upward-facing face (dot(N,pull) > 0.5) that sits below the part top
  //    AND is adjacent (within reach) to a recessed lateral wall found by Strategy C.
  //    This is the "ceiling" of a slot or groove that opens sideways: the die cannot reach
  //    or release it in a straight pull.

  var undercutCrit=[], undercutWarn=[], sidecoreList=[];

  // --- Strategies A & B: single pass ---
  faces.forEach(function(f){
    if(f.empty) return;
    if(f.kind==='planar'){
      var dPull=dot(f.normal,pull);
      if(dPull < -0.087){
        var ucAngle=Math.acos(Math.max(-1,Math.min(1,dPull)))*180/Math.PI - 90;
        f._ucAngle=ucAngle;
        if(ucAngle > 30) undercutCrit.push(f);
        else             undercutWarn.push(f);
      }
    }
    if((f.kind==='cylindrical'||f.kind==='conical') && f.axis){
      if(Math.abs(dot(f.axis,pull)) < 0.5) sidecoreList.push(f);
    }
  });

  // Pull-direction extents (used by C & D)
  var pullExtMin=Infinity, pullExtMax=-Infinity;
  faces.forEach(function(f){
    if(f.empty) return;
    var h=dot(f.centroidMM,pull);
    if(h<pullExtMin) pullExtMin=h;
    if(h>pullExtMax) pullExtMax=h;
  });
  var pullSpan=(pullExtMax-pullExtMin)||1;

  // --- Strategy C setup: collect all lateral planar faces ---
  // Lateral = |dot(N,pull)| < 0.5  (normal within 30° of perpendicular to pull).
  // Exclude backward-facing (already Strategy A).
  var lateralPlanar=[];
  faces.forEach(function(f){
    if(f.empty||f.kind!=='planar') return;
    var dPull=dot(f.normal,pull);
    if(dPull < -0.087) return;           // backward → A
    if(Math.abs(dPull) < 0.5) lateralPlanar.push(f);
  });

  // O(N²) depth-behind: for each lateral face F, how far is F recessed behind the
  // furthest face centroid seen in F's outward-normal direction?
  // depthBehind > 0 means F is hidden inside a pocket rather than on the outer surface.
  // We project ALL face centroids (any kind) onto F's normal — the one that extends furthest
  // in that direction represents the outer surface; F's distance behind it is depthBehind.
  lateralPlanar.forEach(function(f){
    var myExt=dot(f.centroidMM,f.normal), maxExt=myExt;
    for(var gi=0;gi<faces.length;gi++){
      if(faces[gi].empty) continue;
      var e=dot(faces[gi].centroidMM,f.normal);
      if(e>maxExt) maxExt=e;
    }
    f._depthBehind=maxExt-myExt;
  });

  // Classify recessed lateral faces (pocket walls).
  // Reject faces at the very top/bottom of the part (parting-surface geometry).
  var recessedLateral=[];
  lateralPlanar.forEach(function(f){
    var relH=(dot(f.centroidMM,pull)-pullExtMin)/pullSpan;
    var atExtreme=(relH<0.05||relH>0.95);
    if(f._depthBehind > 1.0 || (!atExtreme && f._depthBehind > 0.1))
      recessedLateral.push(f);
  });

  // Strategy C: recessed lateral walls that PASS the draft check (they currently show green).
  // Draft-failing lateral walls are already caught by the draft-check items above.
  var lateralPocketWalls=[];
  recessedLateral.forEach(function(f){
    var angNP=Math.acos(Math.min(1,Math.abs(dot(f.normal,pull))))*180/Math.PI;
    if(Math.abs(angNP-90) >= RULES.draftInsideDeg-1e-6) lateralPocketWalls.push(f);
  });

  // --- Strategy D: enclosed ceiling faces ---
  // An upward-facing face (dot(N,pull) > 0.5) that is:
  //   • below the part top (relH < 0.92), AND
  //   • within "reach" of at least one recessed lateral wall (recessedLateral from C)
  // cannot be released by a straight pull — it is the ceiling of a lateral slot/groove.
  // Reach is adaptive: proportional to the wall face's own size, clamped to 8–40 mm.
  var ceilUndercuts=[];
  if(recessedLateral.length > 0){
    faces.forEach(function(f){
      if(f.empty||f.kind!=='planar') return;
      if(dot(f.normal,pull) <= 0.5) return;           // not upward-facing enough
      var relH=(dot(f.centroidMM,pull)-pullExtMin)/pullSpan;
      if(relH > 0.92) return;                         // at/near top parting surface → OK
      var fPullH=dot(f.centroidMM,pull);
      for(var i=0;i<recessedLateral.length;i++){
        var g=recessedLateral[i];
        // Ceiling must be AT OR ABOVE the lateral wall in the pull direction.
        // A ceiling that is BELOW the wall centroid is not a roof of that wall's pocket.
        if(dot(g.centroidMM,pull) > fPullH) continue;
        var reach=Math.min(Math.max(Math.sqrt(g.areaMM2)*2.0, 8.0), 40.0);
        var dx=f.centroidMM[0]-g.centroidMM[0];
        var dy=f.centroidMM[1]-g.centroidMM[1];
        var dz=f.centroidMM[2]-g.centroidMM[2];
        if(Math.sqrt(dx*dx+dy*dy+dz*dz) < reach){ ceilUndercuts.push(f); break; }
      }
    });
  }

  // --- Report items ---

  // Strategy A — critical undercuts
  if(undercutCrit.length){
    var maxUcAngle=0;
    undercutCrit.forEach(function(f){ if(f._ucAngle>maxUcAngle) maxUcAngle=f._ucAngle; });
    items.push({
      faces:undercutCrit.map(function(f){return f.index;}),
      sev:'crit',
      type:'Undercut — straight pull blocked ('+undercutCrit.length+' face(s))',
      current:undercutCrit.length+' face(s) face backward by up to '+maxUcAngle.toFixed(1)+
              '° past perpendicular to the '+pullName+' pull direction. '+
              'The die cannot release these surfaces in a straight pull — they would lock the part in the cavity.',
      recommended:'Options: (1) redesign the feature with positive draft or a chamfer so it no longer faces backward, '+
                  '(2) reposition the parting line so the undercut geometry moves to the other die half, '+
                  '(3) add side cores / lifters / collapsible cores (significant tooling cost and complexity).',
      ref:RULES.refUndercut, metric:maxUcAngle
    });
  }

  // Strategy A — mild / potential undercuts
  if(undercutWarn.length){
    items.push({
      faces:undercutWarn.map(function(f){return f.index;}),
      sev:'warn',
      type:'Potential undercut — verify pull direction ('+undercutWarn.length+' face(s))',
      current:undercutWarn.length+' face(s) are tilted 5–30° past perpendicular to the pull direction. '+
              'These may be shallow undercuts, parting-line geometry, or negative-draft surfaces.',
      recommended:'Verify that the chosen pull direction matches the actual die-opening axis. '+
                  'If these faces form re-entrant geometry (e.g. a lip or groove), redesign with a positive draft angle. '+
                  'If they sit on the parting surface, ensure adequate shut-off and flash control.',
      ref:RULES.refUndercut, metric:0
    });
  }

  // Strategy B — perpendicular bores
  if(sidecoreList.length){
    var minDia=Infinity;
    sidecoreList.forEach(function(f){ var d=f.radiusMM*2; if(d<minDia) minDia=d; });
    items.push({
      faces:sidecoreList.map(function(f){return f.index;}),
      sev:'warn',
      type:'Side core / slide required — perpendicular bore(s) ('+sidecoreList.length+')',
      current:sidecoreList.length+' cylindrical / conical feature(s) have axes perpendicular '+
              '(within 30°) to the '+pullName+' pull direction. Smallest bore Ø ≈ '+minDia.toFixed(1)+' mm. '+
              'These cannot be formed by the two main die halves.',
      recommended:'Preferred solutions: (1) reorient the bore so its axis aligns with the pull direction, '+
                  '(2) convert to a through-hole on the parting line (no side core needed), '+
                  '(3) accept a side-core / slide mechanism and account for extra tooling cost, '+
                  'wear, and flash risk at the side-core joint.',
      ref:RULES.refHole, metric:minDia
    });
  }

  // Strategy C — lateral pocket walls (passing draft, showing green without this check)
  if(lateralPocketWalls.length){
    items.push({
      faces:lateralPocketWalls.map(function(f){return f.index;}),
      sev:'crit',
      type:'Side core required — lateral pocket / slot walls ('+lateralPocketWalls.length+' face(s))',
      current:lateralPocketWalls.length+' planar face(s) face laterally (normal within 30° of '+
              'perpendicular to the '+pullName+' pull direction) and sit recessed behind outer geometry. '+
              'These walls form a slot, groove, or pocket that opens sideways and cannot be '+
              'formed or released by a straight pull in the '+pullName+' direction.',
      recommended:'Options: (1) add a side core, lifter, or slide to form and release the pocket; '+
                  '(2) redesign the slot/groove to open in the pull direction; '+
                  '(3) split the pocket to the parting line so each die half contributes one wall; '+
                  '(4) machine after casting if volumes allow.',
      ref:RULES.refUndercut, metric:0
    });
  }

  // Strategy D — enclosed ceiling faces
  if(ceilUndercuts.length){
    items.push({
      faces:ceilUndercuts.map(function(f){return f.index;}),
      sev:'crit',
      type:'Side core required — enclosed slot / pocket ceiling ('+ceilUndercuts.length+' face(s))',
      current:ceilUndercuts.length+' upward-facing face(s) lie below the part top AND directly '+
              'adjacent to recessed lateral walls (see Lateral pocket / slot walls item). '+
              'These are the "ceiling" surfaces of features that open sideways: the die cannot '+
              'reach or release them in a straight '+pullName+' pull without a side-core action.',
      recommended:'Options: (1) add side cores / slides to form and release these ceiling surfaces; '+
                  '(2) redesign the pocket so it is open at the top (remove the ceiling — through-slot); '+
                  '(3) extend the pocket to the parting line so the ceiling disappears; '+
                  '(4) machine after casting.',
      ref:RULES.refUndercut, metric:0
    });
  }
  // ---------- end undercut detection ----------

  var order={crit:0,warn:1,info:2};
  items.sort(function(a,b){return order[a.sev]-order[b.sev];});
  items.forEach(function(it,i){it.n=i+1;});
  return items;
}

function run(mesh, stepText, opts){
  opts=opts||{};
  var unit=detectUnit(stepText||'');
  // OpenCASCADE normalizes all STEP geometry to millimetres on read,
  // so mesh coordinates are already mm regardless of the file's modeling unit.
  var scale=1;
  // bbox in mm
  var P=mesh.position, lo=[1e9,1e9,1e9], hi=[-1e9,-1e9,-1e9];
  for(var i=0;i<P.length;i+=3){for(var a=0;a<3;a++){var v=P[i+a]*scale; if(v<lo[a])lo[a]=v; if(v>hi[a])hi[a]=v;}}
  var dim=[hi[0]-lo[0],hi[1]-lo[1],hi[2]-lo[2]];
  var faces=analyzeFaces(mesh, scale);
  // pull axis / direction
  var pull, pn;
  if(opts.pullVec){
    pull=norm(opts.pullVec);
    pn='selected';
  } else if(opts.axis!=null && opts.axis!=='auto' && opts.axis!==''){
    var ai=+opts.axis; pull=[0,0,0]; pull[ai]=1; pn=['X','Y','Z'][ai];
  } else {
    var mi=0; if(dim[1]>dim[mi])mi=1; if(dim[2]>dim[mi])mi=2; pull=[0,0,0]; pull[mi]=1; pn=['X','Y','Z'][mi];
  }
  var items=buildItems(faces, pull, pn);
  var census={planar:0,cylindrical:0,conical:0,empty:0};
  faces.forEach(function(f){census[f.empty?'empty':f.kind]++;});
  return {unit:unit, bbox:{lo:lo,hi:hi,dim:dim}, faces:faces, items:items,
          pull:pull, pullName:pn, census:census, nFaces:faces.length, RULES:RULES, PDF:PDF};
}

var API={run:run, analyzeFaces:analyzeFaces, detectUnit:detectUnit, RULES:RULES, eig3:eig3};
if(typeof module!=='undefined'&&module.exports) module.exports=API;
root.DfMEngine=API;
})(typeof window!=='undefined'?window:globalThis);
