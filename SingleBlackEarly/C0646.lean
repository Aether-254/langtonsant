import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0646 : checkSingleBlackFast (3, -10) 8839 .west (-9, 0) (-19, -17) = true := by
  decide +kernel

end LangtonsAnt
