import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0408 : checkSingleBlackFast (15, -5) 7369 .east (-2, -11) (-17, -13) = true := by
  decide +kernel

end LangtonsAnt
