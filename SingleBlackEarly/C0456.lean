import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0456 : checkSingleBlackFast (17, 10) 9327 .west (-11, -5) (-14, -23) = true := by
  decide +kernel

end LangtonsAnt
