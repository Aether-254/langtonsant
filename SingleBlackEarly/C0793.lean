import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0793 : checkSingleBlackFast (23, -8) 26907 .east (-12, -2) (-27, -24) = true := by
  decide +kernel

end LangtonsAnt
