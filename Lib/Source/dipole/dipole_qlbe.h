/* This file is part of SparQ, a toolbox for qualitative spatial reasoning.
   Copyright (C) 2006, 2007 SFB/TR 8 Spatial Cognition, Project R3-[Q-Shape]
   More info at http://www.sfbtr8.spatial-cognition.de/project/r3/sparq/

  SparQ is free software and has been released under the terms of the GNU
  General Public License version 3 or later. You should have received a
  copy of the GNU General Public License along with this program. If not,
  see <http://www.gnu.org/licenses/>.
*/


#ifndef _DIPOLE_QLBE_
#define _DIPOLE_QLBE_

#define MAX_STRBUF 1024

extern "C" const char* dipole_qualify(const char*, double, double, double, double, double, double, double, double);

extern "C" const char* dipole_qualify_fp(const char*, double, double, double, double, double, double, double, double);

extern "C" const char* dipole_qualify_72(const char*, double, double, double, double, double, double, double, double);


#endif
