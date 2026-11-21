import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0463 : checkSingleBlackFast (17, 13) 6984 .north (-10, 7) (0, -17) = true := by
  decide +kernel

end LangtonsAnt
