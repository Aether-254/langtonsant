import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0678 : checkSingleBlackFast (17, -11) 8685 .west (-14, 6) (-20, -21) = true := by
  decide +kernel

end LangtonsAnt
