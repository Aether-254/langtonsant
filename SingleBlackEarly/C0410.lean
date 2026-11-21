import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0410 : checkSingleBlackFast (16, -6) 6779 .west (-9, 0) (-19, -15) = true := by
  decide +kernel

end LangtonsAnt
