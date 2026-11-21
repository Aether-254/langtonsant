import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0781 : checkSingleBlackFast (25, -15) 10752 .north (-3, -1) (-27, 1) = true := by
  decide +kernel

end LangtonsAnt
