import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0601 : checkSingleBlackFast (19, 16) 31844 .south (-14, -1) (-12, -43) = true := by
  decide +kernel

end LangtonsAnt
