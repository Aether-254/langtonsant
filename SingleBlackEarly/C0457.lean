import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0457 : checkSingleBlackFast (17, 11) 30107 .west (-4, 3) (-40, 4) = true := by
  decide +kernel

end LangtonsAnt
