import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0798 : checkSingleBlackFast (25, -7) 9938 .south (-9, 0) (-20, -11) = true := by
  decide +kernel

end LangtonsAnt
