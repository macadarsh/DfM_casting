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
  refDraft:{clause:'NADCA S-4A-7-15 — Draft Requirements', page:105},
  refFillet:{clause:'NADCA Sec. 6, p.6-4 — Fillets', page:178},
  refHole:{clause:'NADCA P-4A-9 / p.4A-31 — Cored Holes', page:115},
  refWall:{clause:'NADCA p.4A-31/32 — Wall Thickness', page:115}
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
