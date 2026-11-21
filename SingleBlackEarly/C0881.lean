import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0881 : checkSingleBlackFast (-10, -1) 10752 .north (-6, 7) (0, -21) = true := by
  decide +kernel

end LangtonsAnt
