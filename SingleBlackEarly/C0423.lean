import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0423 : checkSingleBlackFast (18, 0) 9616 .north (-1, -5) (-17, -17) = true := by
  decide +kernel

end LangtonsAnt
