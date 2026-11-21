import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0899 : checkSingleBlackFast (-10, 11) 13444 .north (-10, 6) (-4, -22) = true := by
  decide +kernel

end LangtonsAnt
